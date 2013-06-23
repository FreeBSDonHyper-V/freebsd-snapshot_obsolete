/*-
 * Copyright (c) 2009-2012 Microsoft Corp.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice unmodified, this list of conditions, and the following
 *    disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

 /* An implementation of key value pair (KVP) functionality for FreeBSD */ 
/**
 * Code for handling all KVP related messages 
 */

#include <sys/param.h>
#include <sys/kernel.h>
#include <sys/bus.h>
#include <sys/malloc.h>
#include <sys/module.h>
#include <sys/reboot.h>
#include <sys/timetc.h>
#include <sys/types.h>
#include <sys/systm.h>
#include <sys/proc.h>
#include <sys/kthread.h>
#include <sys/socket.h>
#include <sys/syscallsubr.h>
#include <sys/sysproto.h>
#include <sys/un.h>
#include <sys/endian.h>
#include <net/if_arp.h>
#include <dev/hyperv/include/hyperv.h>
#include <dev/hyperv/netvsc/hv_net_vsc.h>
#include "unicode.h"
#include "hv_kvp.h"


#define DEBUG
#define UNUSED_FLAG 1 /* Unused flags in utf routines */
#define KVP_SUCCESS  0
#define kvp_hdr hdr.kvp_hdr
typedef struct hv_kvp_msg hv_kvp_bsd_msg;

static int hv_kvp_ready(void);
static int hv_kvp_transaction_active(void);
static void hv_kvp_transaction_init(uint32_t, hv_vmbus_channel*, uint64_t, uint8_t*);
static void hv_kvp_conn_register(void *p);
static void hv_kvp_process_msg(void *p);
static void hv_negotiate_version(
		struct hv_vmbus_icmsg_hdr*              icmsghdrp,
        struct hv_vmbus_icmsg_negotiate*        negop,
        uint8_t*                                buf);
static hv_work_queue* kvp_work_queue=NULL;
static uint8_t* receive_buffer[1];
static void hv_kvp_callback(void *context);
static void kvp_user_rcv_timer(void *arg);
static int kvp_load(void);
static char* hv_get_guid(int unit);

/*
 * We maintain a global state, assuming only one transaction can be active
 * at any point in time.
 * Inited by the kvp callback routine (utils file) when a valid message is
 * received from the host;
 */
static struct {
	boolean_t kvp_ready; /* indicates if kvp module is ready or not */
	boolean_t in_progress; /* transaction status - active or not */
	uint32_t host_msg_len; /* length of host message */
	hv_vmbus_channel *channelp; /* pointer to channel */
	uint64_t host_msg_id; /* host message id */
	hv_kvp_bsd_msg  *host_kvp_msg; /* current message from the host */
	uint8_t *rcv_buf; /* rcv buffer for communicating with the host*/
	struct callout_handle kvp_rcv_timer; /* user receive block timer */
} kvp_msg_state;


/* We use an alternative, more convenient representation in the generator. */


static unsigned char guid_instance[32]; /* Global Variable to hold GUID Value */

/* Structure is created to handle the GUID formating {AAAAAAAA-BBBB-CCCC-DDDD-EEEEEEEEEEEE} */
static struct guid_extract {
 	char a1[2];       
 	char a2[2];       
 	char a3[2];       
 	char a4[2];       
 	char b1[2];       
 	char b2[2];       
 	char c1[2];       
 	char c2[2];       
	char d[4];
	char e[12];
};

/* 
 * Data Buffer used by kernel for to/from communication with user daemon 
*/
static hv_kvp_bsd_msg  hv_user_kvp_msg; 

static boolean_t conn_ready; /* indicates if connection to daemon done */
static boolean_t register_done; /* indicates daemon registered with driver */

/* Original socket created during connection establishment */
static int sock_fd;

/* Handle to KVP device */ 
struct hv_device* kvp_hv_dev;


/*
 * Check if kvp routines are ready to receive and respond
 */
static int 
hv_kvp_ready(void)
{
	return(kvp_msg_state.kvp_ready);
}


/*
 * Check if kvp transaction is in progres
 */
static int 
hv_kvp_transaction_active(void)
{
	return(kvp_msg_state.in_progress);
}


/*
 * This routine is called whenever a message is received from the host
 */
static void 
hv_kvp_transaction_init(uint32_t rcv_len, hv_vmbus_channel *rcv_channel, 
			uint64_t request_id, uint8_t *rcv_buf)
{
	/* Store all the relevant message details in the global structure */
	kvp_msg_state.in_progress = TRUE;
	kvp_msg_state.host_msg_len = rcv_len;
	kvp_msg_state.channelp = rcv_channel;
	kvp_msg_state.host_msg_id = request_id;
	kvp_msg_state.rcv_buf = rcv_buf;
	kvp_msg_state.host_kvp_msg = (hv_kvp_bsd_msg *)&rcv_buf[
                                sizeof(struct hv_vmbus_pipe_hdr) +
                                sizeof(struct hv_vmbus_icmsg_hdr)];
}

static void
hv_negotiate_version(
        struct hv_vmbus_icmsg_hdr*              icmsghdrp,
        struct hv_vmbus_icmsg_negotiate*        negop,
        uint8_t*                                buf)
{
        int icframe_vercnt;
        int icmsg_vercnt;
        int i;
		#define MAX_SRV_VER 0x7fff

        icmsghdrp->icmsgsize = 0x10;

        negop = (struct hv_vmbus_icmsg_negotiate *) &buf[
                sizeof(struct hv_vmbus_pipe_hdr) +
                        sizeof(struct hv_vmbus_icmsg_hdr)];
        icframe_vercnt = negop->icframe_vercnt;
        icmsg_vercnt = negop->icmsg_vercnt;

		/*
         * Select the framework version number we will
         * support.
         */

        for (i = 0; i < negop->icframe_vercnt; i++) {
                if (negop->icversion_data[i].major <= MAX_SRV_VER)
                        icframe_vercnt = negop->icversion_data[i].major;
        }

        for (i = negop->icframe_vercnt;
                 (i < negop->icframe_vercnt + negop->icmsg_vercnt); i++) {
                if (negop->icversion_data[i].major <= MAX_SRV_VER)
                        icmsg_vercnt = negop->icversion_data[i].major;
        }

        /*
         * Respond with the maximum framework and service
         * version numbers we can support.
         */
        negop->icframe_vercnt = 1;
        negop->icmsg_vercnt = 1;
        negop->icversion_data[0].major = icframe_vercnt;
        negop->icversion_data[0].minor = 0;
        negop->icversion_data[1].major = icmsg_vercnt;
        negop->icversion_data[1].minor = 0;

}


/*
* Function to extract the hn softc GUID value and expand it into
* a global array
*/

static char* 
hv_get_guid(int unit)
{
     struct hv_device *hv_dev;
     hn_softc_t *sc;
     int i;
	 /* Finindg the hn device softc structure and extract GUID data */
     sc = devclass_get_softc(devclass_find("hn"), unit);
     hv_dev = sc->hn_dev_obj;
     for (i = 0; i < 32; i += 2) {
           sprintf(&guid_instance[i], "%02x",
               hv_dev->device_id.data[i / 2]);
     }
     return (guid_instance);
}


/*
 * Establish a UNIX socket connection with user daemon 
 */

static int
kvp_connect_user(void)
{
	int sock_error;
	struct socket_args unix_sock;
	struct sockaddr_un sock_sun;
	struct thread *thread_ptr;

	thread_ptr = curthread;

	/* Open a Unix Domain socket */
	unix_sock.domain = AF_UNIX;
	unix_sock.type = SOCK_STREAM;
	unix_sock.protocol = 0;
	sock_error = socket(thread_ptr, &unix_sock);
	if (sock_error) {
		printf("kvp_connect_user: socket call failed %d\n", sock_error);
                return sock_error;
	}

	/* Try to connect to user daemon using Unix socket */
	sock_fd = thread_ptr->td_retval[0];
	sock_sun.sun_family = AF_UNIX;
	strcpy(sock_sun.sun_path, BSD_SOC_PATH);
	sock_sun.sun_len = sizeof(struct sockaddr_un) - 
		sizeof(sock_sun.sun_path) + strlen(sock_sun.sun_path) + 1;

	sock_error = kern_connect(thread_ptr, sock_fd, 
					(struct sockaddr *)&sock_sun);
	if (sock_error) {
#ifdef DEBUG
                printf("kvp_connect_user:kern_connect failed:err:%d fd:%d\n",
                        sock_error, sock_fd);
#endif
                kern_close(thread_ptr, sock_fd);
        }
        return sock_error;
}


/*
 * Send kvp msg on the established unix socket connection to the user
 */
static int
kvp_send_user(void)
{
	int send_fd, send_error;
	struct uio send_uio;
        struct iovec send_iovec;
	struct thread *thread_ptr = curthread;

	send_fd = sock_fd;
 	
	memset(&send_uio, 0, sizeof(struct uio));
	
	send_iovec.iov_base = (void *)&hv_user_kvp_msg;
	send_iovec.iov_len = sizeof(hv_kvp_bsd_msg);
        send_uio.uio_iov = &send_iovec;
        send_uio.uio_iovcnt = 1;
        send_uio.uio_resid = send_iovec.iov_len;
        send_uio.uio_segflg = UIO_SYSSPACE;


        send_error = kern_writev(thread_ptr, send_fd, &send_uio);
#ifdef DEBUG
	if (send_error) {
        printf("kvp_send_user:kern_writev failed:err:%d fd:%d th:%p\n", 
		send_error, send_fd, thread_ptr);
		printf("kvp_send_user: writev fail:%p\n", 
		thread_ptr->td_proc->p_fd);
	}
	else {
		printf("kvp_send_user: kern_writev success op= %d pool = %d\n", 
		hv_user_kvp_msg.kvp_hdr.operation,hv_user_kvp_msg.kvp_hdr.pool);
	}
#endif
	return (send_error);
}


/*
 * Receive kvp msg on the established unix socket connection from the user
 */
static int
kvp_rcv_user(void)
{
	int rcv_fd, rcv_error=0;
	struct uio rcv_uio;
    struct iovec rcv_iovec;
	struct thread *thread_ptr = curthread;
#ifdef DEBUG1
	struct hv_kvp_msg *toprint;
	int op;
#endif

	rcv_fd = sock_fd;
	memset(&rcv_uio, 0, sizeof(struct uio)); 	
	rcv_iovec.iov_base = (void *)&hv_user_kvp_msg;
	rcv_iovec.iov_len = sizeof(hv_kvp_bsd_msg);
    rcv_uio.uio_iov = &rcv_iovec;
    rcv_uio.uio_iovcnt = 1;
    rcv_uio.uio_resid = rcv_iovec.iov_len;
    rcv_uio.uio_segflg = UIO_SYSSPACE;

	/* Block read */
        rcv_error = kern_readv(thread_ptr, rcv_fd, &rcv_uio);

	if (rcv_error) {
            printf("kvp_rcv_user: kern_readv failed:err:%d fd:%d th:%p\n", 
			rcv_error, rcv_fd, thread_ptr);
	}
#ifdef DEBUG1
	else {
		toprint = (struct hv_kvp_msg *) &hv_user_kvp_msg;
		op = kvp_msg_state.host_kvp_msg->kvp_hdr.operation;
		printf("kvp_rcv_user:kern_readv successful op:%d\n", op);
		if (op == 0)		
		printf("kvp_rcv_user: KVP_OP_GET:Key is : %s value is : %s\n",
		toprint->body.kvp_set.data.key, 
		toprint->body.kvp_set.data.msg_value.value);
		else if (op == 3)
		printf("kvp_rcv_user: ENUMERATE:index is : %d \n", 
			toprint->body.kvp_enum_data.index);
	}
#endif
	return (rcv_error);
}


/*
 * Convert ip related info in umsg from utf8 to utf16 and store in hmsg
 */
static int 
ipinfo_utf8_utf16(hv_kvp_bsd_msg *umsg, hv_kvp_bsd_msg *hmsg)
{
        int err_ip, err_subnet, err_gway, err_dns, err_adap;

	size_t len=0;
        len = utf8_to_utf16((uint16_t *)hmsg->body.kvp_ip_val.ip_addr,
                        MAX_IP_ADDR_SIZE,
                        (char *)umsg->body.kvp_ip_val.ip_addr,
                        strlen((char *)umsg->body.kvp_ip_val.ip_addr),
                        UNUSED_FLAG, &err_ip);
#ifdef DEBUG
	int i;
	printf("\nipinfo_utf8_utf16:ip_address len:%lu\n", len);
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.ip_addr[i]);
#endif

        len = utf8_to_utf16((uint16_t *)hmsg->body.kvp_ip_val.sub_net,
                        MAX_IP_ADDR_SIZE,
                        (char *)umsg->body.kvp_ip_val.sub_net,
                        strlen((char *)umsg->body.kvp_ip_val.sub_net),
                        UNUSED_FLAG, &err_subnet);
#ifdef DEBUG
	printf("\nipinfo_utf8_utf16:sub_net len:%lu\n", len);
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.sub_net[i]);
#endif

        len = utf8_to_utf16((uint16_t *)hmsg->body.kvp_ip_val.gate_way,
                        MAX_GATEWAY_SIZE,
                        (char *)umsg->body.kvp_ip_val.gate_way,
                        strlen((char *)umsg->body.kvp_ip_val.gate_way),
                        UNUSED_FLAG, &err_gway);
#ifdef DEBUG
	printf("\nipinfo_utf8_utf16:gate_way len:%lu\n", len);
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.gate_way[i]);
#endif

        len = utf8_to_utf16((uint16_t *)hmsg->body.kvp_ip_val.dns_addr,
                        MAX_IP_ADDR_SIZE,
                        (char *)umsg->body.kvp_ip_val.dns_addr,
                        strlen((char *)umsg->body.kvp_ip_val.dns_addr),
                        UNUSED_FLAG, &err_dns);
#ifdef DEBUG
	printf("\nipinfo_utf8_utf16:dns_addr len:%lu\n", len);
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.dns_addr[i]);
#endif

        len = utf8_to_utf16((uint16_t *)hmsg->body.kvp_ip_val.adapter_id,
                        MAX_IP_ADDR_SIZE,
                        (char *)umsg->body.kvp_ip_val.adapter_id,
                        strlen((char *)umsg->body.kvp_ip_val.adapter_id),
                        UNUSED_FLAG, &err_adap);
#ifdef DEBUG
	printf("\nipinfo_utf8_utf16:adapter_id len:%lu\n", len);
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.adapter_id[i]);
#endif

        hmsg->body.kvp_ip_val.dhcp_enabled = umsg->body.kvp_ip_val.dhcp_enabled;
        hmsg->body.kvp_ip_val.addr_family = umsg->body.kvp_ip_val.addr_family;
#ifdef DEBUG
	printf("\nipinfo_utf8_utf16:dhcp_enabled:%d addr_family:%d:\n", 
	hmsg->body.kvp_ip_val.dhcp_enabled, hmsg->body.kvp_ip_val.addr_family);
#endif

        return (err_ip | err_subnet | err_gway | err_dns | err_adap);
}

/* 
 * Convert ip related info in hmsg from utf16 to utf8 and store in umsg
 */
static int 
ipinfo_utf16_utf8(hv_kvp_bsd_msg *hmsg, hv_kvp_bsd_msg *umsg)
{
    int err_ip, err_subnet, err_gway, err_dns, err_adap;
	struct guid_extract *id;
	int unit = 0;
	char if_name[4];
	char* guid_data = NULL;
	char buf[38]; 
	int len=16;
	/* Trying to find GUID of Network Device */
	guid_data = hv_get_guid(unit); /* get_guid returns a golabl varaiable */
	id = (struct guid_extract *)guid_data;
	snprintf(buf, sizeof(buf), "%.2s%.2s%.2s%.2s-%.2s%.2s-%.2s%.2s-%.4s-%.12s",
		id->a4,id->a3,id->a2,id->a1,id->b2,id->b1,id->c2,id->c1,id->d,id->e);
	guid_data = NULL;
	/* Creating Interface Name */
	sprintf(if_name,"%s%d","hn",unit);
	/* Note : Need to implement guid extraction for multiple devices */
#ifdef DEBUG
	int i;
	printf("GUID KVP: %s\nif_name: %s  \n",buf,if_name);
	/* buf holds GUID Instance */
	printf("ipinfo_utf16_utf8:adapterId\n");
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.adapter_id[i]);
	printf("\naddr_family:%x dhcp_enabled:%x:", 
		hmsg->body.kvp_ip_val.addr_family,
		hmsg->body.kvp_ip_val.dhcp_enabled);
	printf("ipinfo_utf16_utf8:ip_address\n");
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.ip_addr[i]);
	printf("\nipinfo_utf16_utf8:sub_net\n");
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.sub_net[i]);
	printf("\nipinfo_utf16_utf8:gate_way\n");
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.gate_way[i]);
	printf("\nipinfo_utf16_utf8:dns_addr\n");
	for (i=0; i<=len; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.dns_addr[i]);
#endif
	/* IP Address */
    len = utf16_to_utf8((char *)umsg->body.kvp_ip_val.ip_addr, MAX_IP_ADDR_SIZE,
                        (uint16_t *)hmsg->body.kvp_ip_val.ip_addr,
                        MAX_IP_ADDR_SIZE, UNUSED_FLAG, &err_ip);
	/* Adapter ID : GUID */
	len = utf16_to_utf8((char *)umsg->body.kvp_ip_val.adapter_id,
                        MAX_ADAPTER_ID_SIZE,
                        (uint16_t *)hmsg->body.kvp_ip_val.adapter_id,
                        MAX_ADAPTER_ID_SIZE, UNUSED_FLAG, &err_adap);
	/* Need to implemnet multiple network adapter handler */
	if (strncmp(buf,(char *)umsg->body.kvp_ip_val.adapter_id,16) == 0)
	{
		/* Pass inteface Name */
		printf("GUID Found\n");
		
		strcpy((char *)umsg->body.kvp_ip_val.adapter_id,if_name);
	}
	else
	{
		/* Need to Implment Safe Exit */  
		printf("GUID Not Found\n");
	}
	/* Address Family , DHCP , SUBNET, Gateway, DNS */ 
	umsg->body.kvp_ip_val.addr_family = hmsg->body.kvp_ip_val.addr_family;
        umsg->body.kvp_ip_val.dhcp_enabled = hmsg->body.kvp_ip_val.dhcp_enabled;
        utf16_to_utf8((char *)umsg->body.kvp_ip_val.sub_net, MAX_IP_ADDR_SIZE,
                        (uint16_t *)hmsg->body.kvp_ip_val.sub_net,
                        MAX_IP_ADDR_SIZE, UNUSED_FLAG, &err_subnet);


        utf16_to_utf8((char *)umsg->body.kvp_ip_val.gate_way, MAX_GATEWAY_SIZE,
                        (uint16_t *)hmsg->body.kvp_ip_val.gate_way,
                        MAX_GATEWAY_SIZE, UNUSED_FLAG, &err_gway);

        utf16_to_utf8((char *)umsg->body.kvp_ip_val.dns_addr, MAX_IP_ADDR_SIZE,
                        (uint16_t *)hmsg->body.kvp_ip_val.dns_addr,
                        MAX_IP_ADDR_SIZE, UNUSED_FLAG, &err_dns);

#ifdef DEBUG
	printf("dhcp_enabled:%d \naddr_family:%d\n", 
	umsg->body.kvp_ip_val.dhcp_enabled, umsg->body.kvp_ip_val.addr_family);
	printf("adapter_id=%s\n",(char *)umsg->body.kvp_ip_val.adapter_id);
	printf("ip_addr=%s\n", (char *)umsg->body.kvp_ip_val.ip_addr);
	printf("sub_net=%s\n", (char *)umsg->body.kvp_ip_val.sub_net);
	printf("gate_way=%s\n", (char *)umsg->body.kvp_ip_val.gate_way);
	printf("dns_addr=%s\n", (char *)umsg->body.kvp_ip_val.dns_addr);
#endif
        return (err_ip | err_subnet | err_gway | err_dns | err_adap);
}


/*
 * Prepare a user kvp msg based on host kvp msg (utf16 to utf8)
 * Ensure utf16_utf8 takes care of the additional string terminating char!!
 */


static void
host_user_kvp_msg(void)
{
	int utf_err=0;
	uint32_t value_type;
	hv_kvp_bsd_msg *hmsg = kvp_msg_state.host_kvp_msg;
	hv_kvp_bsd_msg *umsg = &hv_user_kvp_msg;

	umsg->kvp_hdr.operation = hmsg->kvp_hdr.operation;
	umsg->kvp_hdr.pool = hmsg->kvp_hdr.pool;
	
#ifdef DEBUG
	int i;
	printf("\nhost_user_kvp_msg: operation = %d pool = %d\n", 
		umsg->kvp_hdr.operation, umsg->kvp_hdr.pool);
#endif

	switch (umsg->kvp_hdr.operation) {
	case KVP_OP_SET_IP_INFO:
#ifdef DEBUG
		printf("host_user_kvp_msg: in KVP_OP_SET_IP_INFO\n");
#endif
		ipinfo_utf16_utf8(hmsg, umsg);
		break;
	case KVP_OP_GET_IP_INFO:
#ifdef DEBUG
		printf("host_user_kvp_msg: in KVP_OP_GET_IP_INFO adapterId\n");
	for (i=0; i<=16; i++) 
		printf("%x:", hmsg->body.kvp_ip_val.adapter_id[i]);
#endif
        	utf16_to_utf8((char *)umsg->body.kvp_ip_val.adapter_id,
                        MAX_ADAPTER_ID_SIZE,
                        (uint16_t *)hmsg->body.kvp_ip_val.adapter_id,
                        MAX_ADAPTER_ID_SIZE, UNUSED_FLAG, &utf_err);
						
        	umsg->body.kvp_ip_val.addr_family = 
			hmsg->body.kvp_ip_val.addr_family;
#ifdef DEBUG
		printf("\nadapter_id=%s addr_family:%d\n", 
			(char *)umsg->body.kvp_ip_val.adapter_id,
			umsg->body.kvp_ip_val.addr_family);
#endif
		break;
	case KVP_OP_SET:
		value_type = hmsg->body.kvp_set.data.value_type;
		switch (value_type) {
		case REG_SZ:
		umsg->body.kvp_set.data.value_size =
				utf16_to_utf8(
				(char *)umsg->body.kvp_set.data.msg_value.value,
				HV_KVP_EXCHANGE_MAX_VALUE_SIZE - 1,
				(uint16_t *)hmsg->body.kvp_set.data.msg_value.value,
				hmsg->body.kvp_set.data.value_size,
				UNUSED_FLAG, &utf_err);
		/* utf8 encoding */
		umsg->body.kvp_set.data.value_size = 
			umsg->body.kvp_set.data.value_size/2;
				break;

		case REG_U32:
#ifdef DEBUG
			printf("host_user_kvp_msg: in KVP_OP_SET:REG_U32\n");
#endif
			umsg->body.kvp_set.data.value_size =
			sprintf(umsg->body.kvp_set.data.msg_value.value, "%d", 
				hmsg->body.kvp_set.data.msg_value.value_u32) + 1;
			break;

		case REG_U64:
#ifdef DEBUG
			printf("host_user_kvp_msg: in KVP_OP_SET:REG_U64\n");
#endif
			umsg->body.kvp_set.data.value_size =
			sprintf(umsg->body.kvp_set.data.msg_value.value, "%llu", 
				(unsigned long long)
				hmsg->body.kvp_set.data.msg_value.value_u64) + 1;
			break;

		}
		umsg->body.kvp_set.data.key_size =
			utf16_to_utf8(umsg->body.kvp_set.data.key,
			HV_KVP_EXCHANGE_MAX_KEY_SIZE - 1,
			(uint16_t *)hmsg->body.kvp_set.data.key,
			hmsg->body.kvp_set.data.key_size,
			UNUSED_FLAG, &utf_err);
		/* utf8 encoding */
		umsg->body.kvp_set.data.key_size = 
			umsg->body.kvp_set.data.key_size/2;
#ifdef DEBUG
		printf("host_user_kvp_msg:KVP_OP_SET type:%d ksz:%d vsz:%d\n", 
			value_type, umsg->body.kvp_set.data.key_size,
			umsg->body.kvp_set.data.value_size);
#endif
		break;
	case KVP_OP_GET:
		umsg->body.kvp_get.data.key_size =
			utf16_to_utf8(umsg->body.kvp_get.data.key,
			HV_KVP_EXCHANGE_MAX_KEY_SIZE - 1,
			(uint16_t *)hmsg->body.kvp_get.data.key,
			hmsg->body.kvp_get.data.key_size,
			UNUSED_FLAG, &utf_err);
		/* utf8 encoding */
		umsg->body.kvp_get.data.key_size = 
			umsg->body.kvp_get.data.key_size/2;
#ifdef DEBUG
		printf("host_user_kvp_msg: in KVP_OP_GET keysize:%d key:%s\n",
			umsg->body.kvp_get.data.key_size, 
			umsg->body.kvp_get.data.key);
#endif
			break;

	case KVP_OP_DELETE:
		umsg->body.kvp_delete.key_size =
			utf16_to_utf8(umsg->body.kvp_delete.key,
			HV_KVP_EXCHANGE_MAX_KEY_SIZE - 1,
			(uint16_t *)hmsg->body.kvp_delete.key,
			hmsg->body.kvp_delete.key_size,
			UNUSED_FLAG, &utf_err);
		/* utf8 encoding */
		umsg->body.kvp_delete.key_size = 
			umsg->body.kvp_delete.key_size/2; 
#ifdef DEBUG
		printf("host_user_kvp_msg: KVP_OP_DELETE keysize:%d key:%s\n",
			umsg->body.kvp_delete.key_size,
			umsg->body.kvp_delete.key);
#endif
			break;

	case KVP_OP_ENUMERATE:
		umsg->body.kvp_enum_data.index =
			hmsg->body.kvp_enum_data.index;
#ifdef DEBUG
		printf("host_user_kvp_msg: KVP_OP_ENUMERATE index:%d\n",
			umsg->body.kvp_enum_data.index);
#endif
			break;

	default:
		printf("host_user_kvp_msg: Invalid operation : %d\n", 
			umsg->kvp_hdr.operation);
	}

	return;
}


/* 
 * Prepare a host kvp msg based on user kvp msg (utf8 to utf16)
 */
static int
user_host_kvp_msg(void)
{
	int hkey_len=0, hvalue_len=0, utf_err=0;
	struct hv_kvp_exchg_msg_value  *host_exchg_data;
	char    *key_name, *value;

	hv_kvp_bsd_msg *umsg = &hv_user_kvp_msg;
	hv_kvp_bsd_msg *hmsg = kvp_msg_state.host_kvp_msg;

	switch (kvp_msg_state.host_kvp_msg->kvp_hdr.operation) {
	case KVP_OP_GET_IP_INFO:
#ifdef DEBUG
		printf("user_host_kvp_msg: addr_family:%d dhcp_enabled:%d\n",
		umsg->body.kvp_ip_val.addr_family, umsg->body.kvp_ip_val.dhcp_enabled);
		printf("adapterId:%s\n", (char *)umsg->body.kvp_ip_val.adapter_id);
		printf("ip_addr:%s sub_net:%s\n", 
			(char *)umsg->body.kvp_ip_val.ip_addr,
			(char *)umsg->body.kvp_ip_val.sub_net);
		printf("gate_way:%s dns_addr:%s\n", 
			(char *)umsg->body.kvp_ip_val.gate_way, 
			(char *)umsg->body.kvp_ip_val.dns_addr);
#endif
		return(ipinfo_utf8_utf16(umsg, hmsg));

	case KVP_OP_SET_IP_INFO:
	case KVP_OP_SET:
	case KVP_OP_DELETE:
		return (KVP_SUCCESS);

	case KVP_OP_ENUMERATE:
		host_exchg_data = &hmsg->body.kvp_enum_data.data; 
		key_name = umsg->body.kvp_enum_data.data.key;
		hkey_len = utf8_to_utf16((uint16_t *) host_exchg_data->key,
				((HV_KVP_EXCHANGE_MAX_KEY_SIZE / 2) - 2),
				key_name, strlen(key_name), 
				UNUSED_FLAG, &utf_err);
		/* utf16 encoding */
		host_exchg_data->key_size = 2*(hkey_len + 1); 
		value = umsg->body.kvp_enum_data.data.msg_value.value;	
		hvalue_len = 
		utf8_to_utf16( (uint16_t *)host_exchg_data->msg_value.value,
				( (HV_KVP_EXCHANGE_MAX_VALUE_SIZE / 2) - 2),
				value, strlen(value),
				UNUSED_FLAG, &utf_err);
		host_exchg_data->value_size = 2 * (hvalue_len + 1);
		host_exchg_data->value_type = REG_SZ;

#ifdef DEBUG
		printf("user_host_kvp_msg:KVP_OP_ENUMERATE ukey=%s uvalue:%s\n",
		 	key_name, value);
#endif

		if ((hkey_len < 0) || (hvalue_len < 0)) return(HV_E_FAIL);
		return (KVP_SUCCESS);

	case KVP_OP_GET:
		host_exchg_data = &hmsg->body.kvp_get.data;
		value = umsg->body.kvp_get.data.msg_value.value;
		hvalue_len = utf8_to_utf16((uint16_t *) host_exchg_data->msg_value.value,
				((HV_KVP_EXCHANGE_MAX_VALUE_SIZE / 2) - 2),
				value, strlen(value), 
				UNUSED_FLAG, &utf_err);
		/* Convert value size to uft16 */
		host_exchg_data->value_size = 2*(hvalue_len + 1); 
		/* Use values by string */
		host_exchg_data->value_type = REG_SZ; 
#ifdef DEBUG
		printf("user_host_kvp_msg: KVP_OP_GET uvalue:%s hvalue:%s\n", 
			value, host_exchg_data->msg_value.value);
#endif

		if ((hkey_len < 0) || (hvalue_len < 0)) return(HV_E_FAIL);
		return (KVP_SUCCESS);
	default:
		return(HV_E_FAIL);
	}
}


/*
 * Send the response back to the host.
 */
static void
kvp_respond_host(int error)
{
	struct hv_vmbus_icmsg_hdr *hv_icmsg_hdrp;

	if (!hv_kvp_transaction_active()) {
#ifdef DEBUG
		printf("kvp_respond_host: Transaction not active\n");
#endif
		return;
	}

	hv_icmsg_hdrp = (struct hv_vmbus_icmsg_hdr *)
		&kvp_msg_state.rcv_buf[sizeof(struct hv_vmbus_pipe_hdr)];

	if (error) error = HV_E_FAIL;
	hv_icmsg_hdrp->status = error;
	hv_icmsg_hdrp->icflags = 
		HV_ICMSGHDRFLAG_TRANSACTION | HV_ICMSGHDRFLAG_RESPONSE;

	error = hv_vmbus_channel_send_packet(kvp_msg_state.channelp, 
		kvp_msg_state.rcv_buf, 
		kvp_msg_state.host_msg_len, kvp_msg_state.host_msg_id,
		HV_VMBUS_PACKET_TYPE_DATA_IN_BAND, 0);

	if (error) {
		printf("kvp_respond_host: hv_vmbus_channel_send_packet failed error:%d msg_id:%lu, msg_len:%d\n",
		error, kvp_msg_state.host_msg_id, kvp_msg_state.host_msg_len);
	}

	/* Now ready to process another transaction */
	kvp_msg_state.in_progress = FALSE;

	return;
}


/* Timer to establish connection with the user daemon */
static void
kvp_user_rcv_timer(void *arg)
{
	int error=KVP_SUCCESS;
        printf("kvp_user_rcv_timer: timer triggered\n");
	//printf("kvp:guid:%s\n",kvp_hv_dev->class_id);
	
	/* If daemon is already ready, just connect to the host and return */
	if (hv_kvp_ready()) {
		kvp_msg_state.kvp_rcv_timer.callout = NULL;
		error = hv_vmbus_channel_open(kvp_hv_dev->channel, 
					4 * PAGE_SIZE, 4 * PAGE_SIZE, 
				NULL, 0, hv_kvp_callback, kvp_hv_dev->channel);
		if (error) 
			printf("kvp_user_rcv_timer: vmbus_chan_open failed\n");
	}
	else {
		hv_queue_work_item(kvp_work_queue, hv_kvp_conn_register, NULL);
		kvp_msg_state.kvp_rcv_timer = 
			timeout(kvp_user_rcv_timer, NULL, 10);
	}
}


/* 
 * Initiate a connection and receive REGISTER message from the user daemon
 */
void
hv_kvp_conn_register(void *p)
{
	int error=KVP_SUCCESS;
	if (conn_ready == FALSE) {
		/* wait until the user daemon is ready */
		if (kvp_connect_user() != KVP_SUCCESS) {
#ifdef DEBUG
			printf("kvp_conn: Connect to user daemon failed\n");
#endif
			return;
		}
		else {
#ifdef DEBUG
			printf("kvp_conn: Connect to user daemon successful\n");
#endif
			conn_ready = TRUE;
		}
	}

	/* First message from the user should be a KVP_OP_REGISTER msg */
	if (register_done == FALSE) {
		error = kvp_rcv_user(); /* receive a message from user */
		if (hv_user_kvp_msg.kvp_hdr.operation == KVP_OP_REGISTER) {
#ifdef DEBUG
			printf("kvp_conn:Rcvd KVP_OP_REGISTER msg from user\n");
#endif
			/* Cancel timer and establish connection to the host */
			if (kvp_msg_state.kvp_rcv_timer.callout) {
                        	untimeout(kvp_user_rcv_timer, NULL, 
					kvp_msg_state.kvp_rcv_timer);
				 kvp_msg_state.kvp_rcv_timer.callout = NULL;
			}
			error = hv_vmbus_channel_open(kvp_hv_dev->channel, 
					4 * PAGE_SIZE, 4 * PAGE_SIZE, 
				NULL, 0, hv_kvp_callback, kvp_hv_dev->channel);
			if (error) 
				printf("hv_kvp_conn: vmbus_chan_open failed\n");

			register_done = TRUE;
			kvp_msg_state.kvp_ready = TRUE;

		}
	}
}


/**
 * This is the main kvp kernel process that interacts with both user daemon 
 * and the host 
 */
void
hv_kvp_process_msg(void *p)
{
	int error=KVP_SUCCESS; 
	int operation=0;
	/* Prepare kvp_msg to be sent to user */
	host_user_kvp_msg(); 

	/* Send msg to user on Unix Socket */
	error = kvp_send_user();
	if (error != KVP_SUCCESS) {
#ifdef DEBUG
		printf("kvp_process:Send kvp msg to user failed err:%d\n", 
			error);
#endif
		if (error == EPIPE) {
			printf("kvp_process snd:user daemon terminated\n");
			conn_ready = FALSE;
			register_done = FALSE;
			kvp_msg_state.kvp_ready = FALSE;
		}
       		kvp_respond_host(HV_E_FAIL);
		return;
	}

	/* Rcv response from user on Unix Socket */
	hv_user_kvp_msg.hdr.error = HV_E_FAIL;
	error = kvp_rcv_user();
	if ((error == KVP_SUCCESS) && 
		(hv_user_kvp_msg.hdr.error != HV_E_FAIL)) {
		/* Convert user kvp to host kvp and then respond */
		error = user_host_kvp_msg();
		if (error != KVP_SUCCESS) {
			printf("kvp_process:user to host kvpmsg conv failed\n");
			kvp_respond_host(HV_E_FAIL);
		}
		else {
#ifdef DEBUG
			operation = 
				kvp_msg_state.host_kvp_msg->kvp_hdr.operation;
			printf("kvp_process:Msg:%d sent tohost ", operation);
			if (operation == KVP_OP_ENUMERATE) 
				printf("index:%d\n", 
				kvp_msg_state.host_kvp_msg->body.kvp_enum_data.index);
			else
			if ((operation == KVP_OP_GET_IP_INFO) ||
				(operation == KVP_OP_SET_IP_INFO))
				printf("addr_family:%d dhcp_enabled:%d\n", 
					kvp_msg_state.host_kvp_msg->body.kvp_ip_val.addr_family, 
					kvp_msg_state.host_kvp_msg->body.kvp_ip_val.dhcp_enabled);
#endif
                                kvp_respond_host(hv_user_kvp_msg.hdr.error);
		} 
	}
	else {
#ifdef DEBUG	
		printf("kvp_process:Rcv from user failed: err %d %d\n", error, 
			hv_user_kvp_msg.hdr.error);
#endif
		if (error == EPIPE) {
			printf("kvp_process rcv:user daemon terminated\n");
			conn_ready = FALSE;
			register_done = FALSE;
			kvp_msg_state.kvp_ready = FALSE;
		}
		kvp_respond_host(HV_E_FAIL);
	} 
	return;
}


/* 
 * Callback routine that gets called whenever there is a message from host
 */
static 
void hv_kvp_callback(void *context)
{
	uint8_t*		buf;
	hv_vmbus_channel*	channel = context;
	uint32_t		recvlen;
	uint64_t		requestid;
	int			ret;

	struct hv_vmbus_icmsg_hdr*		icmsghdrp;
	buf = receive_buffer[0];

#if 0
	/* If driver unloaded abruptly, return */
	if (vmbus_kvp_channel == NULL) 
	{
#ifdef DEBUG
		printf("hv_kvp_cb: kvp unloaded abruptly\n");
#endif
		return;
	}
#endif

	/* Check if kvp is ready to process */
	if (!hv_kvp_ready()) {
#ifdef DEBUG
		printf("hv_kvp_cb: kvp is not ready..initing\n");
#endif
		hv_queue_work_item(kvp_work_queue, hv_kvp_conn_register, NULL);
	}

	/* Check if already one transaction is under process */
	if (hv_kvp_transaction_active()) {
#ifdef DEBUG
		printf("hv_kvp_cb: Already one transaction is active\n");
#endif
		return;
	}
	ret = hv_vmbus_channel_recv_packet(channel, buf, PAGE_SIZE * 2, 
		&recvlen, &requestid);

#ifdef DEBUG
	printf("hv_kvp_cb: vmbus_recv ret:%d rLen:%d rId:%d\n", 
		ret, recvlen, (int)requestid);
#endif
	if ((ret == 0) && (recvlen > 0)) {

		icmsghdrp = (struct hv_vmbus_icmsg_hdr *)
			&buf[sizeof(struct hv_vmbus_pipe_hdr)];

		if (icmsghdrp->icmsgtype == HV_ICMSGTYPE_NEGOTIATE) {
#ifdef DEBUG
			printf("hv_kvp_cb: Negotiate message received\n");
#endif
			hv_negotiate_version(icmsghdrp, NULL, buf);
		} else {
#ifdef DEBUG
			printf("hv_kvp_cb: New host message received\n");
#endif
			hv_kvp_transaction_init(recvlen,channel,requestid, buf);
			hv_queue_work_item(kvp_work_queue,
						hv_kvp_process_msg, NULL);
			return; /* deferred response by KVP process */
		}

		icmsghdrp->icflags = HV_ICMSGHDRFLAG_TRANSACTION |
			HV_ICMSGHDRFLAG_RESPONSE;

		hv_vmbus_channel_send_packet(channel, buf, recvlen, requestid,
			HV_VMBUS_PACKET_TYPE_DATA_IN_BAND, 0);
	}
}


static 
int kvp_load(void)
{

#ifdef DEBUG
	printf("kvp_load: called\n");
#endif

	/* Allocate twice PAGE_SIZE for KVP */
	receive_buffer[0] = malloc(PAGE_SIZE*2, M_DEVBUF, M_WAITOK | M_ZERO);
	if (receive_buffer[0] == NULL)
	{
		printf("kvp_load: receive_buffer alloc failed\n");
		return(ENOMEM);
	}	

	kvp_work_queue = hv_work_queue_create("KVP Service");
	if (kvp_work_queue == NULL)
	{
		printf("kvp_load: kvp_work_queue alloc failed\n");
        	free(receive_buffer[0], M_DEVBUF);
        	receive_buffer[0] = NULL;
		return(ENOMEM);
	}	

	return (0);
}


static 
int load_kvp_module(struct module *m, int what, void *arg)
{
 int error = 0;
 switch (what)
 {
        case MOD_LOAD:
#ifdef DEBUG
                printf("load_module:loading kvp module \n");
#endif
		kvp_load();
                break;

        default:
                error = EOPNOTSUPP;
                break;
 }
 return error;
}


static int
hv_kvp_probe(device_t dev)
{
	int rtn_value = ENXIO;
	const char *p = vmbus_get_type(dev);

/**
 * Note: GUID codes below are predefined by the host hypervisor
 * (Hyper-V and Azure)interface and required for correct operation.
 */
        /* KVP (Key Value Pair) Service */
 const char kvp_guid[16] = {0xe7, 0xf4, 0xa0, 0xa9, 0x45, 0x5a, 0x96, 0x4d,
							0xb8, 0x27, 0x8a, 0x84, 0x1e, 0x8c, 0x3,  0xe6};

#ifdef DEBUG
	printf("hv_kvp_probe: called\n");
#endif
	if (!memcmp(p, &kvp_guid, sizeof(hv_guid))) {
			device_set_softc(dev, NULL);
#ifdef DEBUG
		printf("hv_kvp_probe: memcmp matched\n");
#endif
			rtn_value = 0;
	}
#ifdef DEBUG
	else printf("hv_kvp_probe: memcmp not matched\n");
#endif

	return rtn_value;
}


static int
hv_kvp_attach(device_t dev)
{
	int	ret = KVP_SUCCESS;
#ifdef DEBUG
	printf("hv_kvp_attach: called\n");
#endif

	kvp_hv_dev = vmbus_get_devctx(dev);
	device_printf(dev, "Hyper-V Service attaching: %s\n", 
		"Hyper-V KVP Service\n");

#if 0
	ret = hv_vmbus_channel_open(hv_dev->channel, 
			2 * PAGE_SIZE, 2 * PAGE_SIZE, 
			NULL, 0, hv_kvp_callback, hv_dev->channel);

	if (ret) printf("hv_kvp_attach: hv_vmbus_channel_open failed\n");
#endif
	kvp_msg_state.kvp_rcv_timer = timeout(kvp_user_rcv_timer, NULL, 10);
	if (kvp_msg_state.kvp_rcv_timer.callout == NULL) {
		printf("hv_kvp_attach: timer creation failed\n");
		ret = -1; 
	}
	return (ret);
}


static int
hv_kvp_detach(device_t dev)
{
	struct hv_device* hv_dev;

#ifdef DEBUG
	printf("hv_kvp_detach: called\n");
#endif
	hv_dev = vmbus_get_devctx(dev);

	if (kvp_hv_dev != hv_dev) 
		printf("hv_kvp_detach: Closing an INVALID kvp device\n");
	hv_vmbus_channel_close(hv_dev->channel);
	kvp_hv_dev = NULL;
	return (0);
}

static void hv_kvp_init(void)
{
}


static device_method_t kvp_methods[] = {
	/* Device interface */
	DEVMETHOD(device_probe, hv_kvp_probe),
	DEVMETHOD(device_attach, hv_kvp_attach),
	DEVMETHOD(device_detach, hv_kvp_detach),
	DEVMETHOD(device_shutdown, bus_generic_shutdown),
	{ 0, 0 } }
;

static driver_t kvp_driver = { "hyperv-kvp", kvp_methods, 0 };

static devclass_t kvp_devclass;

DRIVER_MODULE(hv_kvp, vmbus, kvp_driver, kvp_devclass, load_kvp_module, 0);
MODULE_VERSION(hv_kvp, 1);
MODULE_DEPEND(hv_kvp, vmbus, 1, 1, 1);

SYSINIT(hv_kvp_initx, SI_SUB_RUN_SCHEDULER, SI_ORDER_MIDDLE + 1,
	hv_kvp_init, NULL);
