/*
  Copyright (c) 1999 Rafal Wojtczuk <nergal@7bulls.com>. All rights reserved.
  See the file COPYING for license details.
 */

#include <config.h>
#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <netinet/ip_icmp.h>

#include "checksum.h"
#include "scan.h"
#include "tcp.h"
#include "util.h"
#include "nids.h"
#include "hash.h"

#if ! HAVE_TCP_STATES
enum {
  TCP_ESTABLISHED = 1,
  TCP_SYN_SENT,
  TCP_SYN_RECV,
  TCP_FIN_WAIT1,
  TCP_FIN_WAIT2,
  TCP_TIME_WAIT,
  TCP_CLOSE,
  TCP_CLOSE_WAIT,
  TCP_LAST_ACK,
  TCP_LISTEN,
  TCP_CLOSING			/* now a valid state */
};

#endif

#define FIN_SENT 120
#define FIN_CONFIRMED 121
#define COLLECT_cc 1
#define COLLECT_sc 2
#define COLLECT_ccu 4
#define COLLECT_scu 8

#define EXP_SEQ (snd->first_data_seq + rcv->count + rcv->urg_count)

extern struct proc_node *tcp_procs;

static struct tcp_stream **tcp_stream_table;
static struct tcp_stream *streams_pool;
static int tcp_num = 0;
static int tcp_stream_table_size;
static int max_stream;
static struct tcp_stream *tcp_latest = 0, *tcp_oldest = 0;
static struct tcp_stream *free_streams;
static struct ip *ugly_iphdr;
struct tcp_timeout *nids_tcp_timeouts = 0;
// 释放half_stream的skbuff链表
static void purge_queue(struct half_stream * h)
{
  struct skbuff *tmp, *p = h->list;

  while (p) {
    free(p->data);
    tmp = p->next;
    free(p);
    p = tmp;
  }
  h->list = h->listtail = 0;
  h->rmem_alloc = 0;
}
// 在nids_tcp_timeouts链表中添加a_tcp对应的tcp_timeout超时计时器，按超时时间排序
static void
add_tcp_closing_timeout(struct tcp_stream * a_tcp)
{
  struct tcp_timeout *to;
  struct tcp_timeout *newto;

  /*
  tcp_workarounds
  Enables extra checks for faulty implementations of TCP such as the ones 
  which allow connections to be closed despite the fact that 
  there should be retransmissions for lost packets first (as stated by RFC 793, section 3.5). 
  If non-zero, libnids will set the NIDS_TIMED_OUT state for savagely closed connections. Default value: 0 
  */
  if (!nids_params.tcp_workarounds)
    return;
  newto = malloc(sizeof (struct tcp_timeout));
  if (!newto)
      nids_params.no_mem("add_tcp_closing_timeout");
  newto->a_tcp = a_tcp;
  newto->timeout.tv_sec = nids_last_pcap_header->ts.tv_sec + 10;
  newto->prev = 0;
  for (newto->next = to = nids_tcp_timeouts; to; newto->next = to = to->next) {
    if (to->a_tcp == a_tcp) { // 已经存在
      free(newto);
      return;
    }
    if (to->timeout.tv_sec > newto->timeout.tv_sec) // 按超时时间排序，头部是最先超时的
      break;
    newto->prev = to;
  }
  if (!newto->prev)
    nids_tcp_timeouts = newto;
  else
    newto->prev->next = newto;
  if (newto->next)
    newto->next->prev = newto;
}

// 从nids_tcp_timeouts链表中删除a_tcp对应的tcp_timeout超时计时器
static void
del_tcp_closing_timeout(struct tcp_stream * a_tcp)
{
  struct tcp_timeout *to;

  if (!nids_params.tcp_workarounds)
    return;
  for (to = nids_tcp_timeouts; to; to = to->next) // 遍历nids_tcp_timeouts，查找a_tcp
    if (to->a_tcp == a_tcp)
      break;
  if (!to)
    return;
  if (!to->prev)
    nids_tcp_timeouts = to->next;
  else
    to->prev->next = to->next;
  if (to->next)
    to->next->prev = to->prev;
  free(to);
}
// 释放a_tcp的half_stream的skbuff链表和data，以及listeners链表
// 并将a_tcp从nids_tcp_timeouts链表、tcp_stream_table哈希表、tcp_oldest链表中摘除
// 将a_tcp放会free_streams
void
nids_free_tcp_stream(struct tcp_stream * a_tcp)
{
  int hash_index = a_tcp->hash_index;
  struct lurker_node *i, *j;

  del_tcp_closing_timeout(a_tcp); // 从nids_tcp_timeouts链表中删除a_tcp对应的tcp_timeout超时计时器
  purge_queue(&a_tcp->server);  // 释放half_stream的skbuff链表
  purge_queue(&a_tcp->client);  // 释放half_stream的skbuff链表
   
  if (a_tcp->next_node)  // 将a_tcp从tcp_stream_table中摘除
    a_tcp->next_node->prev_node = a_tcp->prev_node;
  if (a_tcp->prev_node)
    a_tcp->prev_node->next_node = a_tcp->next_node;
  else
    tcp_stream_table[hash_index] = a_tcp->next_node;
  if (a_tcp->client.data)  // 释放half_stream的data
    free(a_tcp->client.data);
  if (a_tcp->server.data)  // 释放half_stream的data
    free(a_tcp->server.data);
  if (a_tcp->next_time)  // 将a_tcp从tcp_oldest、tcp_latest中摘除
    a_tcp->next_time->prev_time = a_tcp->prev_time;
  if (a_tcp->prev_time)
    a_tcp->prev_time->next_time = a_tcp->next_time;
  if (a_tcp == tcp_oldest)
    tcp_oldest = a_tcp->prev_time;
  if (a_tcp == tcp_latest)
    tcp_latest = a_tcp->next_time;
  
  i = a_tcp->listeners;
  
  while (i) { // 释放listeners链表
    j = i->next;
    free(i);
    i = j;
  }
  a_tcp->next_free = free_streams; // 将a_tcp放会free_streams
  free_streams = a_tcp;
  tcp_num--;
}

void
tcp_check_timeouts(struct timeval *now)
{
  struct tcp_timeout *to;
  struct tcp_timeout *next;
  struct lurker_node *i;

  for (to = nids_tcp_timeouts; to; to = next) {
    if (now->tv_sec < to->timeout.tv_sec) // 头部是最先超时的
      return;
    to->a_tcp->nids_state = NIDS_TIMED_OUT;
    for (i = to->a_tcp->listeners; i; i = i->next) // 释放tcp_stream前调用上层应用
      (i->item) (to->a_tcp, &i->data);
    next = to->next;
    nids_free_tcp_stream(to->a_tcp); // 释放对应的tcp_stream
  }
}

static int
mk_hash_index(struct tuple4 addr) // 使用四元组计算哈希值
{
  int hash=mkhash(addr.saddr, addr.source, addr.daddr, addr.dest);
  return hash % tcp_stream_table_size;
}

static int get_ts(struct tcphdr * this_tcphdr, unsigned int * ts)
{
  int len = 4 * this_tcphdr->th_off;
  unsigned int tmp_ts;
  unsigned char * options = (unsigned char*)(this_tcphdr + 1);
  int ind = 0, ret = 0;
  while (ind <=  len - (int)sizeof (struct tcphdr) - 10 )
  	switch (options[ind]) {
		case 0: /* TCPOPT_EOL */
			return ret;
		case 1: /* TCPOPT_NOP */
			ind++;
			continue;	
  		case 8: /* TCPOPT_TIMESTAMP */
	  		memcpy((char*)&tmp_ts, options + ind + 2, 4);
  			*ts=ntohl(tmp_ts);
			ret = 1;
			/* no break, intentionally */
		default:	
			if (options[ind+1] < 2 ) /* "silly option" */
				return ret;
			ind += options[ind+1];
	}			
			
  return ret;
}  		

static int get_wscale(struct tcphdr * this_tcphdr, unsigned int * ws)
{
  int len = 4 * this_tcphdr->th_off;
  unsigned int tmp_ws;
  unsigned char * options = (unsigned char*)(this_tcphdr + 1);
  int ind = 0, ret = 0;
  *ws=1;
  while (ind <=  len - (int)sizeof (struct tcphdr) - 3 )
  	switch (options[ind]) {
		case 0: /* TCPOPT_EOL */
			return ret;
		case 1: /* TCPOPT_NOP */
			ind++;
			continue;	
  		case 3: /* TCPOPT_WSCALE */
  			tmp_ws=options[ind+2];
  			if (tmp_ws>14) 
  				tmp_ws=14;
			*ws=1<<tmp_ws;
			ret = 1;
			/* no break, intentionally */
		default:	
			if (options[ind+1] < 2 ) /* "silly option" */
				return ret;
			ind += options[ind+1];
	}			
			
  return ret;
}  		

    

// 添加tcp_stream，确定C、S关系，client状态TCP_SYN_SENT、server状态TCP_CLOSE
// 新建的tcp_stream会加入tcp_stream_table哈希表和tcp_oldest链表
static void
add_new_tcp(struct tcphdr * this_tcphdr, struct ip * this_iphdr)
{
  struct tcp_stream *tolink;
  struct tcp_stream *a_tcp;
  int hash_index;
  struct tuple4 addr;
  
  addr.source = ntohs(this_tcphdr->th_sport);
  addr.dest = ntohs(this_tcphdr->th_dport);
  addr.saddr = this_iphdr->ip_src.s_addr;
  addr.daddr = this_iphdr->ip_dst.s_addr;
  hash_index = mk_hash_index(addr); // 使用四元组计算哈希值
  
  if (tcp_num > max_stream) { // 当前维持的tcp_stream数量达到最大值，释放最旧的tcp_stream
    struct lurker_node *i;
    int orig_client_state=tcp_oldest->client.state;
    tcp_oldest->nids_state = NIDS_TIMED_OUT;
    for (i = tcp_oldest->listeners; i; i = i->next)
      (i->item) (tcp_oldest, &i->data);
    nids_free_tcp_stream(tcp_oldest);
    if (orig_client_state!=TCP_SYN_SENT)
      nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_TOOMUCH, ugly_iphdr, this_tcphdr);
  }
  a_tcp = free_streams; // 从free_streams头部获取一个可用的tcp_stream
  if (!a_tcp) {
    fprintf(stderr, "gdb me ...\n");
    pause();
  }
  free_streams = a_tcp->next_free;
  
  tcp_num++; // tcp_stream计数加一
  tolink = tcp_stream_table[hash_index];
  memset(a_tcp, 0, sizeof(struct tcp_stream));
  a_tcp->hash_index = hash_index;
  a_tcp->addr = addr; // 此时确定C、S关系
  a_tcp->client.state = TCP_SYN_SENT;
  a_tcp->client.seq = ntohl(this_tcphdr->th_seq) + 1; // 下一个seq
  a_tcp->client.first_data_seq = a_tcp->client.seq;
  a_tcp->client.window = ntohs(this_tcphdr->th_win);
  a_tcp->client.ts_on = get_ts(this_tcphdr, &a_tcp->client.curr_ts); // 获取tcp首部选项部分的时间戳
  a_tcp->client.wscale_on = get_wscale(this_tcphdr, &a_tcp->client.wscale);
  a_tcp->server.state = TCP_CLOSE;
  a_tcp->next_node = tolink; // 插入首部
  a_tcp->prev_node = 0;
  if (tolink)
    tolink->prev_node = a_tcp;
  tcp_stream_table[hash_index] = a_tcp;
  a_tcp->next_time = tcp_latest; // 插入tcp_latest链表首部
  a_tcp->prev_time = 0;
  if (!tcp_oldest)
    tcp_oldest = a_tcp;
  if (tcp_latest)
    tcp_latest->prev_time = a_tcp;
  tcp_latest = a_tcp;
}

static void
add2buf(struct half_stream * rcv, char *data, int datalen)
{
  int toalloc;
  
  if (datalen + rcv->count - rcv->offset > rcv->bufsize) { // 有序数据缓冲区空间不足
    if (!rcv->data) { // 还未分配过空间，首次分配
      if (datalen < 2048)
	toalloc = 4096;
      else
	toalloc = datalen * 2;
      rcv->data = malloc(toalloc);
      rcv->bufsize = toalloc;
    }
    else { // 重新分配空间
      if (datalen < rcv->bufsize)
      	toalloc = 2 * rcv->bufsize;
      else	
      	toalloc = rcv->bufsize + 2*datalen;
      rcv->data = realloc(rcv->data, toalloc);
      rcv->bufsize = toalloc;
    }
    if (!rcv->data)
      nids_params.no_mem("add2buf");
  }
  memcpy(rcv->data + rcv->count - rcv->offset, data, datalen); // 新到的有序数据放入rcv的缓冲区
  rcv->count_new = datalen; // 更新count_new和count
  rcv->count += datalen;
}

static void
ride_lurkers(struct tcp_stream * a_tcp, char mask) // 调用所有上层注册的处理函数，更新关注状态
{
  struct lurker_node *i;
  char cc, sc, ccu, scu;
  
  for (i = a_tcp->listeners; i; i = i->next)
    if (i->whatto & mask) {
      cc = a_tcp->client.collect;
      sc = a_tcp->server.collect;
      ccu = a_tcp->client.collect_urg;
      scu = a_tcp->server.collect_urg;

      (i->item) (a_tcp, &i->data);
      if (cc < a_tcp->client.collect)
	i->whatto |= COLLECT_cc;
      if (ccu < a_tcp->client.collect_urg)
	i->whatto |= COLLECT_ccu;
      if (sc < a_tcp->server.collect)
	i->whatto |= COLLECT_sc;
      if (scu < a_tcp->server.collect_urg)
	i->whatto |= COLLECT_scu;
      if (cc > a_tcp->client.collect)
	i->whatto &= ~COLLECT_cc;
      if (ccu > a_tcp->client.collect_urg)
	i->whatto &= ~COLLECT_ccu;
      if (sc > a_tcp->server.collect)
	i->whatto &= ~COLLECT_sc;
      if (scu > a_tcp->server.collect_urg)
	i->whatto &= ~COLLECT_scu;
    }
}

static void
notify(struct tcp_stream * a_tcp, struct half_stream * rcv)
{
  struct lurker_node *i, **prev_addr;
  char mask;

  if (rcv->count_new_urg) {
    if (!rcv->collect_urg)
      return;
    if (rcv == &a_tcp->client)
      mask = COLLECT_ccu;
    else
      mask = COLLECT_scu;
    ride_lurkers(a_tcp, mask);
    goto prune_listeners;
  }
  if (rcv->collect) {
    if (rcv == &a_tcp->client)
      mask = COLLECT_cc;
    else
      mask = COLLECT_sc;
   do {
	int total;
		a_tcp->read = rcv->count - rcv->offset;
		  total=a_tcp->read;
  
	    ride_lurkers(a_tcp, mask);
	    if (a_tcp->read>total-rcv->count_new) // 只在one_loop_less!=0时有效
	    	rcv->count_new=total-a_tcp->read;
	    
	    if (a_tcp->read > 0) { // a_tcp->read代表上层已经处理的字节数，可以丢弃；默认为当前全部字节数，即全部丢弃，每次回调后rcv->data都会清空；否则丢弃前a_tcp->read字节
	      memmove(rcv->data, rcv->data + a_tcp->read, rcv->count - rcv->offset - a_tcp->read);
	      rcv->offset += a_tcp->read;
	    }
	}while (nids_params.one_loop_less && a_tcp->read>0 && rcv->count_new); 
// we know that if one_loop_less!=0, we have only one callback to notify
   rcv->count_new=0;	    
  }
 prune_listeners: // 清理不再关注该tcp_stream的处理函数
  prev_addr = &a_tcp->listeners;
  i = a_tcp->listeners;
  while (i)
    if (!i->whatto) {
      *prev_addr = i->next;
      free(i);
      i = *prev_addr;
    }
    else {
      prev_addr = &i->next;
      i = i->next;
    }
}

static void
add_from_skb(struct tcp_stream * a_tcp, struct half_stream * rcv,
	     struct half_stream * snd,
	     u_char *data, int datalen,
	     u_int this_seq, char fin, char urg, u_int urg_ptr)
{
  u_int lost = EXP_SEQ - this_seq; // 重叠数据长度
  int to_copy, to_copy2;
  
  if (urg && after(urg_ptr, EXP_SEQ - 1) &&
      (!rcv->urg_seen || after(urg_ptr, rcv->urg_ptr))) {
    rcv->urg_ptr = urg_ptr;
    rcv->urg_seen = 1;
  }
  if (rcv->urg_seen && after(rcv->urg_ptr + 1, this_seq + lost) &&
      before(rcv->urg_ptr, this_seq + datalen)) {
    to_copy = rcv->urg_ptr - (this_seq + lost);
    if (to_copy > 0) {
      if (rcv->collect) {
	add2buf(rcv, (char *)(data + lost), to_copy);
	notify(a_tcp, rcv);
      }
      else {
	rcv->count += to_copy;
	rcv->offset = rcv->count; /* clear the buffer */
      }
    }
    rcv->urgdata = data[rcv->urg_ptr - this_seq];
    rcv->count_new_urg = 1;
    notify(a_tcp, rcv);
    rcv->count_new_urg = 0;
    rcv->urg_seen = 0;
    rcv->urg_count++;
    to_copy2 = this_seq + datalen - rcv->urg_ptr - 1;
    if (to_copy2 > 0) {
      if (rcv->collect) {
	add2buf(rcv, (char *)(data + lost + to_copy + 1), to_copy2);
	notify(a_tcp, rcv);
      }
      else {
	rcv->count += to_copy2;
	rcv->offset = rcv->count; /* clear the buffer */
      }
    }
  }
  else {
    if (datalen - lost > 0) { // 本次实际新就绪数据长度
      if (rcv->collect) { // rcv设置了关注
	add2buf(rcv, (char *)(data + lost), datalen - lost); // 把新到的有序数据放入rcv的缓冲区
	notify(a_tcp, rcv);
      }
      else { // rcv不关注
	rcv->count += datalen - lost;
	rcv->offset = rcv->count; /* clear the buffer */
      }
    }
  }
  if (fin) {
    snd->state = FIN_SENT;
    if (rcv->state == TCP_CLOSING)
      add_tcp_closing_timeout(a_tcp); // 在nids_tcp_timeouts链表中添加a_tcp对应的tcp_timeout超时计时器，按超时时间排序
  }
}

static void
tcp_queue(struct tcp_stream * a_tcp, struct tcphdr * this_tcphdr,
	  struct half_stream * snd, struct half_stream * rcv,
	  char *data, int datalen, int skblen
	  )
{
  u_int this_seq = ntohl(this_tcphdr->th_seq);
  struct skbuff *pakiet, *tmp;
  
  /*
   * Did we get anything new to ack?
   */
  // #define EXP_SEQ (snd->first_data_seq + rcv->count + rcv->urg_count)
  // EXP_SEQ是目前已集齐的数据流水号，我们希望收到从这里开始的数据
  if (!after(this_seq, EXP_SEQ)) { // 先判断数据是不是在EXP_SEQ之前开始  
    if (after(this_seq + datalen + (this_tcphdr->th_flags & TH_FIN), EXP_SEQ)) { // 再判断数据长度是不是在EXP_SEQ之后，如果是，说明有新数据，否则是重发的包，无视之
      /* the packet straddles our window end */
      get_ts(this_tcphdr, &snd->curr_ts);
      // 更新集齐的数据区，值得一提的是add_from_skb函数一旦发现集齐了一段数据之后  
      // 便立刻调用notify函数，在notify函数里面将数据推给回调方
      add_from_skb(a_tcp, rcv, snd, (u_char *)data, datalen, this_seq,
		   (this_tcphdr->th_flags & TH_FIN),
		   (this_tcphdr->th_flags & TH_URG),
		   ntohs(this_tcphdr->th_urp) + this_seq - 1);
      /*
       * Do we have any old packets to ack that the above
       * made visible? (Go forward from skb)
       */
      // 此时EXP_SEQ有了变化了，看看缓冲区里的包有没有符合条件能用同样的方法处理掉的  
      // 有就处理掉，然后释放
      pakiet = rcv->list;
      while (pakiet) {
	if (after(pakiet->seq, EXP_SEQ)) // 缓存的最小seq在EXP_SEQ之后，无法处理，需要等待
	  break;
	if (after(pakiet->seq + pakiet->len + pakiet->fin, EXP_SEQ)) { // 数据长度在EXP_SEQ之后，说明有新数据
	  add_from_skb(a_tcp, rcv, snd, pakiet->data,
		       pakiet->len, pakiet->seq, pakiet->fin, pakiet->urg,
		       pakiet->urg_ptr + pakiet->seq - 1);
        }
	rcv->rmem_alloc -= pakiet->truesize; // 释放掉这个pakiet
	if (pakiet->prev)
	  pakiet->prev->next = pakiet->next;
	else
	  rcv->list = pakiet->next;
	if (pakiet->next)
	  pakiet->next->prev = pakiet->prev;
	else
	  rcv->listtail = pakiet->prev;
	tmp = pakiet->next;
	free(pakiet->data);
	free(pakiet);
	pakiet = tmp;
      }
    }
    else
      return;
  }
  else { // 这里说明现在这个包是个乱序到达的（数据开始点超过了EXP_SEQ），放到缓冲区等待处理，注意保持缓冲区有序
    struct skbuff *p = rcv->listtail;

    pakiet = mknew(struct skbuff);
    pakiet->truesize = skblen;
    rcv->rmem_alloc += pakiet->truesize;
    pakiet->len = datalen;
    pakiet->data = malloc(datalen);
    if (!pakiet->data)
      nids_params.no_mem("tcp_queue");
    memcpy(pakiet->data, data, datalen);
    pakiet->fin = (this_tcphdr->th_flags & TH_FIN);
    /* Some Cisco - at least - hardware accept to close a TCP connection
     * even though packets were lost before the first TCP FIN packet and
     * never retransmitted; this violates RFC 793, but since it really
     * happens, it has to be dealt with... The idea is to introduce a 10s
     * timeout after TCP FIN packets were sent by both sides so that
     * corresponding libnids resources can be released instead of waiting
     * for retransmissions which will never happen.  -- Sebastien Raveau
     */
    if (pakiet->fin) {
      snd->state = TCP_CLOSING;
      if (rcv->state == FIN_SENT || rcv->state == FIN_CONFIRMED)
	add_tcp_closing_timeout(a_tcp); // 在nids_tcp_timeouts链表中添加a_tcp对应的tcp_timeout超时计时器，按超时时间排序
    }
    pakiet->seq = this_seq;
    pakiet->urg = (this_tcphdr->th_flags & TH_URG);
    pakiet->urg_ptr = ntohs(this_tcphdr->th_urp);
    for (;;) {
      if (!p || !after(p->seq, this_seq)) // 查找插入位置，按seq排序
	break;
      p = p->prev;
    }
    if (!p) {
      pakiet->prev = 0;
      pakiet->next = rcv->list;
      if (rcv->list)
         rcv->list->prev = pakiet;
      rcv->list = pakiet;
      if (!rcv->listtail)
	rcv->listtail = pakiet;
    }
    else {
      pakiet->next = p->next;
      p->next = pakiet;
      pakiet->prev = p;
      if (pakiet->next)
	pakiet->next->prev = pakiet;
      else
	rcv->listtail = pakiet;
    }
  }
}

static void
prune_queue(struct half_stream * rcv, struct tcphdr * this_tcphdr)
{
  struct skbuff *tmp, *p = rcv->list;

  nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_BIGQUEUE, ugly_iphdr, this_tcphdr);
  while (p) {
    free(p->data);
    tmp = p->next;
    free(p);
    p = tmp;
  }
  rcv->list = rcv->listtail = 0;
  rcv->rmem_alloc = 0;
}
// 更新snd->ack_seq
static void
handle_ack(struct half_stream * snd, u_int acknum)
{
  int ackdiff;

  ackdiff = acknum - snd->ack_seq;
  if (ackdiff > 0) {
    snd->ack_seq = acknum;
  }
}
#if 0
static void
check_flags(struct ip * iph, struct tcphdr * th)
{
  u_char flag = *(((u_char *) th) + 13);
  if (flag & 0x40 || flag & 0x80)
    nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_BADFLAGS, iph, th);
//ECN is really the only cause of these warnings...
}
#endif
// 查找对应的tcp_stream，并确定方向
struct tcp_stream *
find_stream(struct tcphdr * this_tcphdr, struct ip * this_iphdr,
	    int *from_client)
{
  struct tuple4 this_addr, reversed;
  struct tcp_stream *a_tcp;

  this_addr.source = ntohs(this_tcphdr->th_sport);
  this_addr.dest = ntohs(this_tcphdr->th_dport);
  this_addr.saddr = this_iphdr->ip_src.s_addr;
  this_addr.daddr = this_iphdr->ip_dst.s_addr;
  a_tcp = nids_find_tcp_stream(&this_addr); // 根据四元组，查找对应的tcp_stream
  if (a_tcp) {
    *from_client = 1;
    return a_tcp;
  }
  reversed.source = ntohs(this_tcphdr->th_dport);
  reversed.dest = ntohs(this_tcphdr->th_sport);
  reversed.saddr = this_iphdr->ip_dst.s_addr;
  reversed.daddr = this_iphdr->ip_src.s_addr;
  a_tcp = nids_find_tcp_stream(&reversed); // 调换源、目的，查找对应的tcp_stream
  if (a_tcp) {
    *from_client = 0;
    return a_tcp;
  }
  return 0;
}
// 根据四元组，查找对应的tcp_stream
struct tcp_stream *
nids_find_tcp_stream(struct tuple4 *addr)
{
  int hash_index;
  struct tcp_stream *a_tcp;

  hash_index = mk_hash_index(*addr); // 使用四元组计算哈希值
  for (a_tcp = tcp_stream_table[hash_index];
       a_tcp && memcmp(&a_tcp->addr, addr, sizeof (struct tuple4));
       a_tcp = a_tcp->next_node);
  return a_tcp ? a_tcp : 0;
}

// 释放tcp_stream_table和streams_pool
void tcp_exit(void)
{
  int i;
  struct lurker_node *j;
  struct tcp_stream *a_tcp, *t_tcp;

  if (!tcp_stream_table || !streams_pool)
    return;
  for (i = 0; i < tcp_stream_table_size; i++) { // 遍历哈希表项
    a_tcp = tcp_stream_table[i];
    while(a_tcp) { // 释放tcp_stream_table[i]指向的tcp_stream链表
      t_tcp = a_tcp;
      a_tcp = a_tcp->next_node;
      for (j = t_tcp->listeners; j; j = j->next) { // 释放tcp_stream前，调用listeners
          t_tcp->nids_state = NIDS_EXITING;
	  (j->item)(t_tcp, &j->data);
      }
      nids_free_tcp_stream(t_tcp);  // 释放a_tcp的half_stream的skbuff链表和data，以及listeners链表；并将a_tcp从nids_tcp_timeouts链表、tcp_stream_table哈希表、tcp_oldest链表中摘除；将a_tcp放会free_streams
    }
  }
  free(tcp_stream_table); // 释放tcp_stream_table哈希表
  tcp_stream_table = NULL;
  free(streams_pool); // 释放tcp_stream池
  streams_pool = NULL;
  /* FIXME: anything else we should free? */
  /* yes plz.. */
  tcp_latest = tcp_oldest = NULL;
  tcp_num = 0;
}
// 处理一个完整的ip包，并且负载是tcp协议
void
process_tcp(u_char * data, int skblen)
{
  struct ip *this_iphdr = (struct ip *)data; // 指向ip首部
  struct tcphdr *this_tcphdr = (struct tcphdr *)(data + 4 * this_iphdr->ip_hl); // 指向tcp首部
  int datalen, iplen; // TCP数据部分的长度，IP包的长度
  int from_client = 1;
  unsigned int tmp_ts;
  struct tcp_stream *a_tcp;
  struct half_stream *snd, *rcv;

  ugly_iphdr = this_iphdr;
  iplen = ntohs(this_iphdr->ip_len); // ip包总长度
  if ((unsigned)iplen < 4 * this_iphdr->ip_hl + sizeof(struct tcphdr)) { // 校验长度
    nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_HDR, this_iphdr,
		       this_tcphdr);
    return;
  } // ktos sie bawi
  
  datalen = iplen - 4 * this_iphdr->ip_hl - 4 * this_tcphdr->th_off; // 总长度 - ip首部长度 - tcp首部长度 = tcp负载长度
  
  if (datalen < 0) {
    nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_HDR, this_iphdr,
		       this_tcphdr);
    return;
  } // ktos sie bawi

  if ((this_iphdr->ip_src.s_addr | this_iphdr->ip_dst.s_addr) == 0) { // sip，dip全为0，返回
    nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_HDR, this_iphdr,
		       this_tcphdr);
    return;
  }
  if (!(this_tcphdr->th_flags & TH_ACK))
    detect_scan(this_iphdr);
  if (!nids_params.n_tcp_streams) return; // tcp_stream_table为空，不处理
  if (my_tcp_check(this_tcphdr, iplen - 4 * this_iphdr->ip_hl,
		   this_iphdr->ip_src.s_addr, this_iphdr->ip_dst.s_addr)) {
    nids_params.syslog(NIDS_WARN_TCP, NIDS_WARN_TCP_HDR, this_iphdr,
		       this_tcphdr);
    return;
  }
#if 0
  check_flags(this_iphdr, this_tcphdr);
//ECN
#endif
  if (!(a_tcp = find_stream(this_tcphdr, this_iphdr, &from_client))) { // 查找对应的tcp_stream，并确定方向
    if ((this_tcphdr->th_flags & TH_SYN) &&
	!(this_tcphdr->th_flags & TH_ACK) &&
	!(this_tcphdr->th_flags & TH_RST)) // 没有找到对应的tcp_stream，处理第一个syn包
      add_new_tcp(this_tcphdr, this_iphdr); // 添加tcp_stream，确定C、S关系，client状态TCP_SYN_SENT、server状态TCP_CLOSE；新建的tcp_stream会加入tcp_stream_table哈希表和tcp_oldest链表
    return;
  }
  if (from_client) { // 确定方向
    snd = &a_tcp->client;
    rcv = &a_tcp->server;
  }
  else {
    rcv = &a_tcp->client;
    snd = &a_tcp->server;
  }
  if ((this_tcphdr->th_flags & TH_SYN)) {
    if (from_client || a_tcp->client.state != TCP_SYN_SENT ||
      a_tcp->server.state != TCP_CLOSE || !(this_tcphdr->th_flags & TH_ACK)) // 这里，我们期望看到S->C的syn&ack包，不是则丢弃
      return;
    if (a_tcp->client.seq != ntohl(this_tcphdr->th_ack)) // 判断发送端的ack是否等于接收端的seq
      return;
    a_tcp->server.state = TCP_SYN_RECV;
    a_tcp->server.seq = ntohl(this_tcphdr->th_seq) + 1;
    a_tcp->server.first_data_seq = a_tcp->server.seq;
    a_tcp->server.ack_seq = ntohl(this_tcphdr->th_ack);
    a_tcp->server.window = ntohs(this_tcphdr->th_win);
    if (a_tcp->client.ts_on) {
    	a_tcp->server.ts_on = get_ts(this_tcphdr, &a_tcp->server.curr_ts); // 尝试获取tcp首部选项部分的时间戳
	if (!a_tcp->server.ts_on)
		a_tcp->client.ts_on = 0;
    } else a_tcp->server.ts_on = 0;	
    if (a_tcp->client.wscale_on) {
    	a_tcp->server.wscale_on = get_wscale(this_tcphdr, &a_tcp->server.wscale); // 尝试获取tcp首部选项部分的wscale
	if (!a_tcp->server.wscale_on) {
		a_tcp->client.wscale_on = 0;
		a_tcp->client.wscale  = 1;
		a_tcp->server.wscale = 1;
	}	
    } else {
    	a_tcp->server.wscale_on = 0;	
    	a_tcp->server.wscale = 1;
    }	
    return; // syn&ack处理完毕，返回
  }
  if (
  	! (  !datalen && ntohl(this_tcphdr->th_seq) == rcv->ack_seq  ) // 不是流水号正确且没数据的包
  	&&
  	( !before(ntohl(this_tcphdr->th_seq), rcv->ack_seq + rcv->window*rcv->wscale) || // seq在rcv的滑动窗口之外，不正常
          before(ntohl(this_tcphdr->th_seq) + datalen, rcv->ack_seq)  // 重复数据，已经ack过
        )
     )     
     return;

  if ((this_tcphdr->th_flags & TH_RST)) { // 处理rst包
    if (a_tcp->nids_state == NIDS_DATA) {
      struct lurker_node *i;

      a_tcp->nids_state = NIDS_RESET;
      for (i = a_tcp->listeners; i; i = i->next)
	(i->item) (a_tcp, &i->data);
    }
    nids_free_tcp_stream(a_tcp);
    return;
  }

  /* PAWS check */
  if (rcv->ts_on && get_ts(this_tcphdr, &tmp_ts) && 
  	before(tmp_ts, snd->curr_ts)) // 校验时间戳
  return; 	
  
  if ((this_tcphdr->th_flags & TH_ACK)) {
    if (from_client && a_tcp->client.state == TCP_SYN_SENT &&
	a_tcp->server.state == TCP_SYN_RECV) { // 处理第三次握手C->S的ack包
      if (ntohl(this_tcphdr->th_ack) == a_tcp->server.seq) { // client端的ack等于server端的seq，tcp连接成功建立
	a_tcp->client.state = TCP_ESTABLISHED;
	a_tcp->client.ack_seq = ntohl(this_tcphdr->th_ack);
	{
	  struct proc_node *i;
	  struct lurker_node *j;
	  void *data;
	  
	  a_tcp->server.state = TCP_ESTABLISHED;
	  a_tcp->nids_state = NIDS_JUST_EST;
	  for (i = tcp_procs; i; i = i->next) { // 调用注册的tcp处理函数，进行认领该tcp_stream，可能有多个处理函数认领该tcp_stream
	    char whatto = 0;
	    char cc = a_tcp->client.collect;
	    char sc = a_tcp->server.collect;
	    char ccu = a_tcp->client.collect_urg;
	    char scu = a_tcp->server.collect_urg;
	    
	    (i->item) (a_tcp, &data);
	    if (cc < a_tcp->client.collect)
	      whatto |= COLLECT_cc;  // 1，collect client data
	    if (ccu < a_tcp->client.collect_urg)
	      whatto |= COLLECT_ccu; // 4，collect client urgent data
	    if (sc < a_tcp->server.collect)
	      whatto |= COLLECT_sc; // 2，collect server data
	    if (scu < a_tcp->server.collect_urg)
	      whatto |= COLLECT_scu; // 8，collect server urgent data
	    if (nids_params.one_loop_less) {
	    		if (a_tcp->client.collect >=2) {
	    			a_tcp->client.collect=cc;
	    			whatto&=~COLLECT_cc;
	    		}
	    		if (a_tcp->server.collect >=2 ) {
	    			a_tcp->server.collect=sc;
	    			whatto&=~COLLECT_sc;
	    		}
	    }  
	    if (whatto) { // 有处理函数需要处理该tcp_stream，添加一个lurker_node
	      j = mknew(struct lurker_node);
	      j->item = i->item;
	      j->data = data;
	      j->whatto = whatto;
	      j->next = a_tcp->listeners;
	      a_tcp->listeners = j;
	    }
	  }
	  if (!a_tcp->listeners) { // 没有处理函数需要这个tcp_stream，释放
	    nids_free_tcp_stream(a_tcp);
	    return;
	  }
	  a_tcp->nids_state = NIDS_DATA;
	}
      }
      // return;
    }
  }
  if ((this_tcphdr->th_flags & TH_ACK)) {
    handle_ack(snd, ntohl(this_tcphdr->th_ack)); // 更新snd->ack_seq
    if (rcv->state == FIN_SENT) // 处理四次挥手
      rcv->state = FIN_CONFIRMED;
    if (rcv->state == FIN_CONFIRMED && snd->state == FIN_CONFIRMED) { // 处理四次挥手
      struct lurker_node *i;

      a_tcp->nids_state = NIDS_CLOSE;
      for (i = a_tcp->listeners; i; i = i->next)
	(i->item) (a_tcp, &i->data);
      nids_free_tcp_stream(a_tcp);
      return;
    }
  }
  if (datalen + (this_tcphdr->th_flags & TH_FIN) > 0)
    tcp_queue(a_tcp, this_tcphdr, snd, rcv,
	      (char *) (this_tcphdr) + 4 * this_tcphdr->th_off,
	      datalen, skblen);
  snd->window = ntohs(this_tcphdr->th_win);
  if (rcv->rmem_alloc > 65535)
    prune_queue(rcv, this_tcphdr);
  if (!a_tcp->listeners)
    nids_free_tcp_stream(a_tcp);
}

void
nids_discard(struct tcp_stream * a_tcp, int num)
{
  if (num < a_tcp->read)
    a_tcp->read = num;
}

void
nids_register_tcp(void (*x))
{
  register_callback(&tcp_procs, x);
}

void
nids_unregister_tcp(void (*x))
{
  unregister_callback(&tcp_procs, x);
}

// 初始化tcp_stream_table和streams_pool，以及init_hash、nids_tcp_timeouts
// size：tcp_stream_table的大小
int
tcp_init(int size)
{
  int i;
  struct tcp_timeout *tmp;

  if (!size) return 0;
  tcp_stream_table_size = size;
  tcp_stream_table = calloc(tcp_stream_table_size, sizeof(char *)); // 分配哈希表空间
  if (!tcp_stream_table) {
    nids_params.no_mem("tcp_init");
    return -1;
  }
  max_stream = 3 * tcp_stream_table_size / 4; // 使用总长度的3/4，这样哈希表的查找效率比较高
  streams_pool = (struct tcp_stream *) malloc((max_stream + 1) * sizeof(struct tcp_stream)); // 分配tcp_stream池
  if (!streams_pool) {
    nids_params.no_mem("tcp_init");
    return -1;
  }
  for (i = 0; i < max_stream; i++)
    streams_pool[i].next_free = &(streams_pool[i + 1]); // 将tcp_stream组织成链表，数组模拟的链表
  streams_pool[max_stream].next_free = 0;
  free_streams = streams_pool;
  init_hash(); // 初始化哈希函数
  while (nids_tcp_timeouts) { // 清空nids_tcp_timeouts超时计时器链表
    tmp = nids_tcp_timeouts->next;
    free(nids_tcp_timeouts);
    nids_tcp_timeouts = tmp;
  }
  return 0;
}

#if HAVE_ICMPHDR
#define STRUCT_ICMP struct icmphdr
#define ICMP_CODE   code
#define ICMP_TYPE   type
#else
#define STRUCT_ICMP struct icmp
#define ICMP_CODE   icmp_code
#define ICMP_TYPE   icmp_type
#endif

#ifndef ICMP_DEST_UNREACH
#define ICMP_DEST_UNREACH ICMP_UNREACH
#define ICMP_PROT_UNREACH ICMP_UNREACH_PROTOCOL
#define ICMP_PORT_UNREACH ICMP_UNREACH_PORT
#define NR_ICMP_UNREACH   ICMP_MAXTYPE
#endif				

// 处理一个完整的ip包，并且负载是icmp协议，只处理目的不可达的情况，用于清理tcp连接
void
process_icmp(u_char * data)
{
  struct ip *iph = (struct ip *) data;
  struct ip *orig_ip;
  STRUCT_ICMP *pkt;
  struct tcphdr *th;
  struct half_stream *hlf;
  int match_addr;
  struct tcp_stream *a_tcp;
  struct lurker_node *i;

  int from_client;
  /* we will use unsigned, to suppress warning; we must be careful with
     possible wrap when substracting 
     the following is ok, as the ip header has already been sanitized */
  unsigned int len = ntohs(iph->ip_len) - (iph->ip_hl << 2); // ip负载长度
  
  if (len < sizeof(STRUCT_ICMP))
    return;
  pkt = (STRUCT_ICMP *) (data + (iph->ip_hl << 2)); // 指向icmp首部
  if (ip_compute_csum((char *) pkt, len))
    return;
  if (pkt->ICMP_TYPE != ICMP_DEST_UNREACH) // 只处理目的不可达
    return;
  /*
目的不可达(Destination Unreachable Message)

0                   1                   2                   3

0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1

+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

|     Type      |     Code      |          Checksum             |

+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

|                             unused                            |

+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

|      Internet Header + 64 bits of Original Data Datagram      |

+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+  
  */

  /* ok due to check 7 lines above */  
  len -= sizeof(STRUCT_ICMP); // icmp负载长度
  // sizeof(struct icmp) is not what we want here
  
  if (len < sizeof(struct ip))
    return;

  orig_ip = (struct ip *) (((char *) pkt) + 8); // 负载中的ip首部
  if (len < (unsigned)(orig_ip->ip_hl << 2) + 8)
     return;
  /* subtraction ok due to the check above */
  len -= orig_ip->ip_hl << 2;
  if ((pkt->ICMP_CODE & 15) == ICMP_PROT_UNREACH ||
      (pkt->ICMP_CODE & 15) == ICMP_PORT_UNREACH)
    match_addr = 1;
  else
    match_addr = 0;
  if (pkt->ICMP_CODE > NR_ICMP_UNREACH)
    return;
  if (match_addr && (iph->ip_src.s_addr != orig_ip->ip_dst.s_addr))
    return;
  if (orig_ip->ip_p != IPPROTO_TCP)
    return;
  th = (struct tcphdr *) (((char *) orig_ip) + (orig_ip->ip_hl << 2)); // 负载中的tcp首部
  if (!(a_tcp = find_stream(th, orig_ip, &from_client)))
    return;
  if (a_tcp->addr.dest == iph->ip_dst.s_addr)
    hlf = &a_tcp->server;
  else
    hlf = &a_tcp->client;
  if (hlf->state != TCP_SYN_SENT && hlf->state != TCP_SYN_RECV)
    return;
  a_tcp->nids_state = NIDS_RESET;
  for (i = a_tcp->listeners; i; i = i->next)
    (i->item) (a_tcp, &i->data);
  nids_free_tcp_stream(a_tcp);
}
