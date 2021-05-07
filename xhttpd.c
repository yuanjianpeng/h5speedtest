#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/sendfile.h>
#include <dirent.h>
#include <libgen.h>
#include <signal.h>
#include <inttypes.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdint.h>
#include <endian.h>

struct mime {
	const char *suffix, *mime;
} mimes[] = {
	{ "js", "application/x-javascript" },
	{ "css", "text/css" },
	{ "htm", "text/html" },
	{ "html", "text/html" },
	{ "txt", "text/plain" },
	{ "pdf", "application/pdf" },
	{ "png", "image/png" },
	{ "git", "image/gif" },
	{ "bmp", "image/bmp" },
	{ "jpg", "image/jpeg" },
	{ "jpeg", "image/jpeg" },
	{ "mp3", "audio/mpeg" },
	{ "wma", "audio/x-ms-wma" },
	{ "wav", "audio/x-wav" },
	{ "mp4", "video/mp4" },
};

struct req
{
#define GET 0
#define POST 1
	int type;
	char *url;
	char *file;
	char *real_file;
	int header_len;
	int content_len;
	int body_remain_len;

	/* Range header */
	int range;
	int64_t range_st, range_en, range_len;

	/* websocket */
	int websocket;
	char *ws_key;
    int frame_head_len;
    uint8_t frame_head[10];
    int64_t frame_payload_len;
    int websocket_end;
    
    /* is cgi */
    int cgi;

    /* pseudo file */
    int pseudo;

	int64_t file_len;
	int is_dir;
	int is_root;
	char *dir_buf;
	const char *mime;
};

void base64(unsigned char *in, int in_len, char *out)
{
	int bits = 0, val = 0;
	char codes[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
	unsigned char *end = in + in_len;

	while (in < end) {
		val = (val << 8) | *in;
		bits += 8;
		while (bits >= 6) {
			*out++ = codes[val >> (bits - 6)];
			val &= (1 << (bits - 6)) - 1;
			bits -= 6;
		}
		in++;
	}
	if (bits) {
		*out++ = codes[val << (6 - bits)];
		*out++ = '=';
		if (bits == 2)
			*out++ = '=';
	}
	*out = '\0';
}

static void one_shot_sha1(char *input, int len, char *digest)
{

#define W(t) w[(t) & 0x0F]
#define CH(x, y, z) (((x) & (y)) | (~(x) & (z)))
#define PARITY(x, y, z) ((x) ^ (y) ^ (z))
#define MAJ(x, y, z) (((x) & (y)) | ((x) & (z)) | ((y) & (z)))
#define ROL32(a, n) (((a) << (n)) | ((a) >> (32 - (n))))
#define MIN(a, b) ((a) < (b) ? (a) : (b))

	uint32_t k[4] = { 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xCA62C1D6 },
		 h[5] = { 0x67452301, 0xEFCDAB89, 0x98BADCFE,0x10325476, 0xC3D2E1F0},
		 w[16], sz, temp, t, a, b, c, d, e;
	int done = 0;
	uint64_t bits = len * 8;
	unsigned char pad = 0x80;

	while (!done) {
		if (len > 0) {
			t = MIN(len, 64);
			memcpy(w, input, t);
			input += t;
			len -= t;
			sz = t;
		}
		else
			sz = 0;
		if (sz < 56) {
			((unsigned char *)w)[sz] = pad;
			for (t = sz + 1; t < 56; t++)
				((unsigned char *)w)[t] = 0;
			w[14] = htobe32((uint32_t)(bits >> 32));
			w[15] = htobe32((uint32_t)bits);
			done = 1;
		}
		else if (sz < 64) {
			((unsigned char *)w)[sz] = pad;
			pad = 0;
			for (t = sz + 1; t < 64; t++)
				((unsigned char *)w)[t] = 0;
		}

		for (t = 0; t < 16; t++)
			w[t] = be32toh(w[t]);

		a = h[0]; b = h[1]; c = h[2]; d = h[3]; e = h[4];
		for (t = 0; t < 80; t++) {
			if(t >= 16)
				W(t) = ROL32(W(t + 13) ^ W(t + 8) ^ W(t + 2) ^ W(t), 1);
			if(t < 20)
				temp = ROL32(a, 5) + CH(b, c, d) + e + W(t) + k[0];
			else if(t < 40)
				temp = ROL32(a, 5) + PARITY(b, c, d) + e + W(t) + k[1];
			else if(t < 60)
				temp = ROL32(a, 5) + MAJ(b, c, d) + e + W(t) + k[2];
			else
				temp = ROL32(a, 5) + PARITY(b, c, d) + e + W(t) + k[3];
			e = d;
			d = c;
			c = ROL32(b, 30);
			b = a;
			a = temp;
		}
		h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e;
	}

	for (t = 0; t < 5; t++)
		((uint32_t *)digest)[t] = htobe32(h[t]);
}

static void usage()
{
	fprintf(stderr, "xhttpd [-d] [-p port] [-C root]\n");
	exit(1);
}

static void get_mime(struct req *req)
{
	char path[1024];
	char *s, *s2;
	int i;

	if (strlen(req->real_file) >= sizeof(path))
		return;
	strcpy(path, req->real_file);
	s = basename(path);
	s2 = strchr(s, '.');
	if (s2 == NULL)
		return;
    if (!strcmp(s2, ".cgi"))
        req->cgi = 1;
	for (i = 0; i < sizeof(mimes)/sizeof(mimes[0]); i++) {
		if (!strcmp(s2 + 1, mimes[i].suffix)) {
			req->mime = mimes[i].mime;
			return;
		}
	}
}

static int parse_first_line(char *buf, int len, struct req *req)
{
	char *tmp;

	if (len < 5)
		return -1;

	/* parse type */
	if (memcmp(buf, "GET ", 4) == 0)
		req->type = GET;
	else if (memcmp(buf, "POST ", 5) == 0)
		req->type = POST;
	else
		return -1;

	/* parse url */
	buf += (req->type == GET) ? 4 : 5;
	len -= (req->type == GET) ? 4 : 5;
	if (len < 2 || (tmp = memmem(buf, len, " ", 1)) == NULL)
		return -1;

	req->url = strndup(buf, tmp - buf);
	if (req->url == NULL || *(req->url) != '/')
		return -1;

	tmp = strchr(req->url, '?');
	req->file = strndup(req->url, tmp ? tmp - req->url : strlen(req->url));
	if (req->file == NULL)
		return -1;
	if (strlen(req->file) == 1) {
		req->is_root = 1;
		req->real_file = strdup(".");
	}
	else {
		req->real_file = strdup(req->file + 1);
	}
	if (req->real_file == NULL)
		return -1;

	printf("pid %d process %s\n", getpid(), req->file);
	return 0;
}

int parse_content_length(char *buf, int len, struct req *req)
{
	return 0;
}

int parse_range(char *buf, int len, struct req *req)
{
	char *tmp = memmem(buf, len, "bytes=", 6);
	if (tmp == NULL)
		return -1;
	len -= tmp - buf + 6;
	buf = tmp + 6;
	if (memchr(buf, ',', len)) {
		fprintf(stderr, "can't support multiple range\n");
		return -1;
	}
	req->range = 1;
	req->range_st = strtoull(buf, &tmp, 10);
	if (buf == tmp)
		return -1;
	tmp = memchr(buf, '-', len);
	if (tmp) {
		buf = tmp + 1;
		req->range_en = strtoull(buf, &tmp, 10);
		if (buf != tmp)
			req->range = 2;
	}

	return 0;
}

int parse_upgrade(char *buf, int len, struct req *req)
{
	int i;

	for (i = 0; i < len; i++) {
		if (buf[i] != ' ')
			break;
	}
	if (len - i == 9 && !memcmp(buf + i, "websocket", 9))
		req->websocket = 1;
	return 0;
}

int parse_websocket_key(char *buf, int len, struct req *req)
{
	int i;

	for (i = 0; i < len; i++) {
		if (buf[i] != ' ')
			break;
	}

	req->ws_key = strndup(buf + i, len - i);
	return 0;
}

struct header_parser
{
	const char *name;
	int (*parser)(char *buf, int len, struct req *req);
} parsers[] = {
	{ "Content-Length", parse_content_length },
	{ "Range", parse_range },
	{ "Upgrade", parse_upgrade },
	{ "Sec-WebSocket-Key", parse_websocket_key },
};

static int _parse_header(char *buf, int len, struct req *req)
{
	int i;
	char *tmp;

	tmp = memchr(buf, ':', len);
	if (tmp == NULL)
		return -1;

	for (i = 0; i < sizeof(parsers)/sizeof(parsers[0]); i++) { 
		if (tmp - buf  == strlen(parsers[i].name)
			&& ! memcmp(buf, parsers[i].name, tmp - buf)) {
			len -= tmp - buf + 1;
			buf = tmp + 1;
			return parsers[i].parser(buf, len, req);
		}
	}

	return 0;
}

static int parse_header(char *buf, int len, struct req *req)
{
	char *tmp;
	int head = 1;
	
	while (tmp = memmem(buf, len, "\r\n", 2)) {
		if (head) {
			if (parse_first_line(buf, tmp - buf, req))
				return -1;
			head = 0;
		} else {
			if (tmp == buf) {
				req->body_remain_len = len - 2;
				return 1;
			}
			if (_parse_header(buf, tmp - buf, req))
				return -1;
		}

		len -= (tmp + 2 - buf);
		buf = tmp + 2;
	}

	return 0;
}

static int read_req(int fd, struct req *req)
{
	char buf[2048];
	int len = 0, ret, state = 0;

	while (1) {
		ret = read(fd, buf + len, sizeof(buf) - len);
		if (ret < 0) {
			fprintf(stderr, "read() failed: %s\n", strerror(errno));
			return -1;
		}
		else if (ret == 0) {
			fprintf(stderr, "client shutdown write\n");
			return -1;
		}
		if (state == 0) {
			len += ret;
			ret = parse_header(buf, len, req);
			if (ret < 0) {
				fprintf(stderr, "invalid header\n");
				return -1;
			}
			else if (ret == 0) /* partial header */
				continue;
			/* finish read header */
			if (req->body_remain_len == 0)
				break;
			len = 0;
			state = 1;
		}
		else {
			req->body_remain_len -= ret;
			if (req->body_remain_len <= 0)
				break;
		}
	}

	return 0;
}

static int write_buf(int fd, char *buf, int buflen)
{
	int ret, len = 0;
	while (len < buflen) {
		ret = write(fd, buf + len, buflen - len);
		if (ret < 0) {
			fprintf(stderr, "write() failed: %s\n",
				strerror(errno));
			return 1;
		}
		else if (ret == 0) {
			fprintf(stderr, "client shutdown recv\n");
			return 1;
		}
		len += ret;
	}
	return 0;
}

static int res_404(int fd, const char *file)
{
	char buf[1024];
	int len;
	len = snprintf(buf, sizeof(buf),
			"HTTP/2 404 Not Found\r\n"
			"\r\n"
			"\"%s\" Not Found",
			file);
	return write_buf(fd, buf, len);
}

static int gene_ws_key(struct req *req, char *key)
{
	char key1[128];
	char sha1[20];
	int n;
	if (req->ws_key == NULL)
		return 0;
	n = snprintf(key1, sizeof(key1), "%s%s",
		req->ws_key, "258EAFA5-E914-47DA-95CA-C5AB0DC85B11");
	one_shot_sha1(key1, n, sha1);
	base64(sha1, 20, key);
}

static int res_header(int fd, struct req *req)
{
	char buf[1024];
	char key[40];
	int len;

	if (req->range) {
		if (req->range == 1) {
			if (req->range_st < 0)
				req->range_st = req->file_len + req->range_st;
			req->range_en = req->file_len - 1;
		}
		if (req->range_st < 0) req->range_st = 0;
		if (req->range_en < 0) req->range_en = 0;
		if (req->range_st > req->range_en || req->range_en > req->file_len)
			return -1;
		req->range_len = req->range_en - req->range_st + 1;
		if (req->range_len > req->file_len)
			req->range_len = req->file_len;
		len = snprintf(buf, sizeof(buf),
			"HTTP/1.1 206 Partial Content\r\n"
			"Content-Range: bytes %" PRId64 "-%" PRId64 "/%" PRId64 "\r\n"
			"Accept-Ranges: bytes\r\n"
			"Content-Length: %" PRId64 "\r\n"
			"\r\n", req->range_st, req->range_en, req->file_len, req->range_len);
	}
	else if (req->websocket) {
		if (gene_ws_key(req, key))
			return -1;
		len = snprintf(buf, sizeof(buf),
			"HTTP/1.1 101 Switching Protocols\r\n"
			"Upgrade: websocket\r\n"
			"Connection: Upgrade\r\n"
			"Sec-WebSocket-Accept: %s\r\n"
			"\r\n", key);
	}
	else {
		len = snprintf(buf, sizeof(buf),
				"HTTP/1.1 200 OK\r\n"
				"Content-Length: %" PRId64 "\r\n",
				req->file_len);
		if (req->mime) {
			len += snprintf(buf + len, sizeof(buf) - len, 
				"Content-Type: %s\r\n", req->mime);
		}
		len += snprintf(buf + len, sizeof(buf) - len, "\r\n");
	}
	return write_buf(fd, buf, len);
}

static int read_dir(struct req *req)
{
	struct dirent *ent;
	DIR *dir;
	char *buf;
	int bufsiz = 128 * 1024, len;
	const char *add_slash = "/";
	char *parent_dir;

	if (req->file[strlen(req->file)-1] == '/')
		add_slash = "";

	buf = malloc(bufsiz);
	if (buf == NULL) {
		fprintf(stderr, "malloc failed: %s\n", strerror(errno));
		return 1;
	}

	dir = opendir(req->real_file);
	if (dir == NULL) {
		fprintf(stderr, "opendir %s failed: %s\n",
				req->file, strerror(errno));
		return 1;
	}

	len = snprintf(buf, bufsiz,
        "<html><head><meta name=\"viewport\" content=\"width=device-width; initial-scale=1;\" /></head><body>"
		"<h1>Index of %s</h1>"
		"<table><tr><th>Name</th><th>Size</th></tr>"
		"<tr><th colspan=2><hr></th></tr>",
		req->file);

	if (!req->is_root) {
		parent_dir = strdup(req->file);
		if (parent_dir == NULL)
			return 1;
		parent_dir = dirname(parent_dir);
		len += snprintf(buf + len, bufsiz - len,
			"<tr><td colspan=2>"
			"<a href=\"%s\">Parent Directory</a></td></tr>",
			parent_dir);
	}

	while (ent = readdir(dir)) {
		if (!strcmp(ent->d_name, ".") || !strcmp(ent->d_name, ".."))
			continue;
		if (ent->d_type != DT_REG && ent->d_type != DT_DIR
            && ent->d_type != DT_LNK)
			continue;
		len += snprintf(buf + len, bufsiz - len,
			"<tr/><td><a href=\"%s%s%s\">%s%s</a></td>"
			"<td align=right>%s</td></tr>",
			req->file, add_slash, ent->d_name,
			ent->d_name, ent->d_type == DT_DIR ? "/" : "", "");
	}

	len += snprintf(buf + len, bufsiz - len, "</table></body></html>");
	req->dir_buf = buf;
	req->file_len = len;
	return 0;
}

/*
    https://datatracker.ietf.org/doc/html/rfc6455

      0                   1                   2                   3
      0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
     +-+-+-+-+-------+-+-------------+-------------------------------+
     |F|R|R|R| opcode|M| Payload len |    Extended payload length    |
     |I|S|S|S|  (4)  |A|     (7)     |             (16/64)           |
     |N|V|V|V|       |S|             |   (if payload len==126/127)   |
     | |1|2|3|       |K|             |                               |
     +-+-+-+-+-------+-+-------------+ - - - - - - - - - - - - - - - +
     |     Extended payload length continued, if payload len == 127  |
     + - - - - - - - - - - - - - - - +-------------------------------+
     |                               |Masking-key, if MASK set to 1  |
     +-------------------------------+-------------------------------+
     | Masking-key (continued)       |          Payload Data         |
     +-------------------------------- - - - - - - - - - - - - - - - +
     :                     Payload Data continued ...                :
     + - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - +
     |                     Payload Data continued ...                |
     +---------------------------------------------------------------+

 */

static int process_ws_buf(unsigned char *buf, int buflen, struct req *req)
{
    int remain = buflen;
    unsigned char h1, h2, payload;

    while (remain > 0) {
        if (req->frame_payload_len > 0) {
            if (remain >= req->frame_payload_len) {
                remain -= req->frame_payload_len;
                req->frame_payload_len = 0;
            }
            else {
                req->frame_payload_len -= remain;
                remain = 0;
            }
        }
        if (req->frame_payload_len == 0) {
            if (remain < 2)
                break;
            h1 = buf[buflen - remain];
            h2 = buf[buflen - remain + 1];
            if ( (h1 & 0x70) || (h2 & 0x80) == 0) {
                fprintf(stderr, "invalid websocket data\n");
                return -1;
            }
            if ( (h1 & 0xf) == 0x8) { /* connection close */
                fprintf(stderr, "websocket: receive close frame (pid %d)\n", getpid());
                return 1;
            }
            payload = h2 & 0x7f;
            if (payload < 126) {
                req->frame_payload_len = payload + 4;   /* 4bytes mask key */
                remain -= 2;
            }
            else if (payload == 126) {
                if (remain < 4)
                    break;
                req->frame_payload_len = 4 + (uint16_t)htobe16(*(uint16_t *)(buf + buflen - remain + 2));
                remain -= 4;
            }
            else {
                if (remain < 10)
                    break;
                req->frame_payload_len = 4 + (uint64_t)htobe64(*(uint64_t *)(buf + buflen - remain + 2));
                remain -= 10;
            }
        }
    }

    if (remain)
        memcpy(req->frame_head, buf + buflen - remain, remain);
    req->frame_head_len = remain;
    return 0;
}

/* for speedtest
    eat all msg, close the websocket if frame received
 */
static int service_ws_upload(int fd, struct req *req, int once)
{
	char buf[8192];
	int ret;
    int flags = 0;

    if (once)
        flags = MSG_DONTWAIT;

    do {
        if (req->frame_head_len)
            memcpy(buf, req->frame_head, req->frame_head_len);
		ret = recv(fd, buf + req->frame_head_len,
                sizeof(buf) - req->frame_head_len, flags);
		if (ret < 0) {
            if (errno == EAGAIN)
                return 1;
			fprintf(stderr, "read() failed: %s\n", strerror(errno));
			return -1;
		}
		else if (ret == 0) {
			fprintf(stderr, "client shutdown write\n");
			return 0;
		}
        ret = process_ws_buf(buf, ret + req->frame_head_len, req);
        if (ret < 0)
            return 0;
        /* client request close websocket */
        else if (ret > 0) {
            buf[0] = 0x81; buf[1] = 0x00;
            write(fd, buf, 2);
            return 0;
        }
	} while (!once);

    return 1;
}

static int add_websocket_head(char *buf, int len)
{
	uint8_t h1, h2;
	uint16_t payload_len16;
    uint64_t payload_len64;
    int hlen = 2;

    h1 = 0x80 | 0x2;
    if (len < 126)
        h2 = len;
    else if (len <= 65535) {
        h2 = 126;
        payload_len16 = len;
        *(uint16_t *)(buf - 2) = htobe16(payload_len16);
        hlen = 4;
    }
    else {
        h2 = 127;
        payload_len64 = len;
        *(uint64_t *)(buf - 8) = htobe64(payload_len64);
        hlen = 10;
    }
    buf[-hlen] = h1;
    buf[-hlen+1] = h2;
    return hlen;
}

static int res_pseudo(int fd, struct req *req)
{
    /* the bufsiz is very important for websocket speedtest
        if it's too large, then the message belong to previous
        or later second affect the result largely, the jitter is bigger
	   If it's too small, then client need more js events to process
	   week cpu may limit the test result.
	 */
    int bufsiz = 1024 * 1024;
    char *buf = malloc(bufsiz);
    int hlen = 0;
    if (buf == NULL)
        return 1;
    memset(buf, 0, bufsiz);
    if (req->websocket) {
        buf += 10;
        bufsiz -= 10;
    }
    while (req->file_len > 0) {
        int len = bufsiz;
        if (len > req->file_len)
            len = req->file_len;
        if (req->websocket)
            hlen = add_websocket_head(buf, len);
        if (write_buf(fd, buf - hlen, len + hlen))
            break;
        req->file_len -= len;
		if (service_ws_upload(fd, req, 1) <= 0)
            break;
    }
    req->websocket_end = 1;
    return 1;
}

static int res_file(int fd, struct req *req)
{
	int filefd, ret;
	int64_t remain = req->file_len;

	filefd = open(req->real_file, O_RDONLY);
	if (filefd < 0) {
		fprintf(stderr, "open %s failed: %s\n",
			req->real_file, strerror(errno));
		return 1;
	}

	if (req->range) {
		remain = req->range_len;
		if ((off_t)-1 == lseek(filefd, req->range_st, SEEK_SET)) {
			fprintf(stderr, "lseek %s failed: %s\n",
					req->real_file, strerror(errno));
			return 1;
		}
	}

	while (remain > 0) {
		ret = sendfile(fd, filefd, NULL, 4094*1024);
		if (ret < 0) {
			fprintf(stderr, "sendfile() failed: %s\n",
				strerror(errno));
			return 1;
		}
		else if (ret == 0) {
			fprintf(stderr, "client shutdown recv\n");
			return 1;
		}
		remain -= ret;
	}

	return 0;
}

static int write_res(int fd, struct req *req)
{
	int filefd, ret;
	struct stat statbuf;
    char buf[8192];

	ret = stat(req->real_file, &statbuf);
	if (ret < 0) {
        ret = readlink(req->real_file, buf, sizeof(buf));
        if (ret <= 0 || ret >= sizeof(buf)) {
            res_404(fd, req->file);
            return 1;
        }
        buf[ret] = '\0';
        req->pseudo = 1;
        req->file_len = strtoul(buf, NULL, 0);
	}
	if (S_ISREG(statbuf.st_mode)) {
		req->is_dir = 0;
		req->file_len = statbuf.st_size;
		get_mime(req);
	}
	else if (S_ISDIR(statbuf.st_mode)) {
		req->is_dir = 1;
		if (read_dir(req))
			return 1;
        req->mime = "text/html";
	}

	if (res_header(fd, req))
		return 1;

    if (req->is_dir)
        ret = write_buf(fd, req->dir_buf, req->file_len);
    else if (req->pseudo)
        ret = res_pseudo(fd, req);
    else
        ret = res_file(fd, req);

    if (req->websocket && !req->websocket_end)
		service_ws_upload(fd, req, 0);

    return ret;
}

static int process_req(int fd, struct sockaddr_in *addr)
{
	struct req req = {0};

	printf("Process request from: %s:%d (pid %d)\n",
			inet_ntoa(addr->sin_addr),
			ntohs(addr->sin_port), getpid());

	if (read_req(fd, &req) < 0)
		return 1;

	return write_res(fd, &req);
}

int main(int argc, char **argv)
{
	int sock, ret, port = 80, daemonlize = 0, opt;
	struct sockaddr_in addr;
	const char *webroot = NULL;

	while ((opt = getopt(argc, argv, "C:dp:")) != -1 ) {
		switch(opt) {
		case 'C':
			webroot = optarg;
			break;
		case 'p':
			port = atoi(optarg);
			break;
		case 'd':
			daemonlize = 1;
			break;
		default:
			fprintf(stderr, "unknown option\n");
		case 'h':
			usage();
		}
	}

	if (webroot && chdir(webroot) < 0) {
		fprintf(stderr, "chdir to %s failed: %s\n",
				webroot, strerror(errno));
		return 1;
	}

	if (signal(SIGCHLD, SIG_IGN) == SIG_ERR) {
		fprintf(stderr, "ignore SIGCHLD failed: %s\n", strerror(errno));
		return 1;
	}

	sock = socket(AF_INET, SOCK_STREAM, 0);
	if (sock < 0) {
		fprintf(stderr, "socket() failed: %s\n", strerror(errno));
		return 1;
	}

	opt = 1;
	ret = setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
	if (ret < 0) {
		fprintf(stderr, "setsockopt() failed: %s\n", strerror(errno));
		return 1;
	}

	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_port = htons(port);
	ret = bind(sock, (struct sockaddr *)&addr, sizeof(addr));
	if (ret < 0) {
		fprintf(stderr, "bind to port %d failed: %s\n",
				port, strerror(errno));
		goto errret;
	}

	ret = listen(sock, 5);
	if (ret < 0) {
		fprintf(stderr, "listen() failed: %s\n", strerror(errno));
		goto errret;
	}

	opt = fcntl(sock, F_GETFD);
	opt |= FD_CLOEXEC;
	fcntl(sock, F_SETFD, opt);

	if (daemonlize && daemon(1, 0) < 0) {
		fprintf(stderr, "daemon() failed: %s\n", strerror(errno));
		goto errret;
	}

	while (1) {
		struct sockaddr_in caddr;
		int cli;
		socklen_t caddr_len = sizeof(caddr);

		cli = accept(sock, (struct sockaddr *)&caddr, &caddr_len);
		if (cli < 0) {
			fprintf(stderr, "accept failed: %s\n", strerror(errno));
			goto errret;
		}
		ret = fork();
		if (ret < 0)
			fprintf(stderr, "fork() failed: %s\n", strerror(errno));
		else if (ret == 0)
			return process_req(cli, &caddr);
		close(cli);
	}

errret:
	close(sock);
	return 1;
}

