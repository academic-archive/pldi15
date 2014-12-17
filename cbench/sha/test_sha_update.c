void memcpy(void *dst, void *src, int n) {
	char *d = dst, *s = src;
	while (n > 0) {
		*d = *s;
		d = d+1;
		s = s+1;
		n = n-1;
	}
}

void memset(void *p, int i, int n) {
	char *c = p;
	while (n > 0) {
		*c = i;
		c = c+1;
		n = n-1;
	}
}

typedef unsigned char BYTE;
typedef unsigned long LONG;


typedef struct {
    LONG digest[5];
    LONG count_lo, count_hi;
    LONG data[16];
} SHA_INFO;

static void sha_transform(SHA_INFO *sha_info)
{
    int i;
    LONG temp, A, B, C, D, E, W[80];

    for (i = 0; i < 16; ++i) {
 W[i] = sha_info->data[i];
    }
    for (i = 16; i < 80; ++i) {
 W[i] = W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16];



    }
    A = sha_info->digest[0];
    B = sha_info->digest[1];
    C = sha_info->digest[2];
    D = sha_info->digest[3];
    E = sha_info->digest[4];
    for (i = 0; i < 20; ++i) {
 temp = ((A << 5) | (A >> (32 - 5))) + ((B & C) | (~B & D)) + E + W[i] + 0x5a827999L; E = D; D = C; C = ((B << 30) | (B >> (32 - 30))); B = A; A = temp;
    }
    for (i = 20; i < 40; ++i) {
 temp = ((A << 5) | (A >> (32 - 5))) + (B ^ C ^ D) + E + W[i] + 0x6ed9eba1L; E = D; D = C; C = ((B << 30) | (B >> (32 - 30))); B = A; A = temp;
    }
    for (i = 40; i < 60; ++i) {
 temp = ((A << 5) | (A >> (32 - 5))) + ((B & C) | (B & D) | (C & D)) + E + W[i] + 0x8f1bbcdcL; E = D; D = C; C = ((B << 30) | (B >> (32 - 30))); B = A; A = temp;
    }
    for (i = 60; i < 80; ++i) {
 temp = ((A << 5) | (A >> (32 - 5))) + (B ^ C ^ D) + E + W[i] + 0xca62c1d6L; E = D; D = C; C = ((B << 30) | (B >> (32 - 30))); B = A; A = temp;
    }

    sha_info->digest[0] += A;
    sha_info->digest[1] += B;
    sha_info->digest[2] += C;
    sha_info->digest[3] += D;
    sha_info->digest[4] += E;
}



void sha_update(SHA_INFO *sha_info, BYTE *buffer, int count)
{
    if ((sha_info->count_lo + ((LONG) count << 3)) < sha_info->count_lo) {
 ++sha_info->count_hi;
    }
    sha_info->count_lo += (LONG) count << 3;
    sha_info->count_hi += (LONG) count >> 29;
    while (count >= 64) {
memcpy(sha_info->data, buffer, 64);



 sha_transform(sha_info);
 buffer += 64;
 count -= 64;
    }
    memcpy(sha_info->data, buffer, count);
}

void start()
{
	SHA_INFO *sha_info;
	BYTE *buffer;
	int count;
	sha_update(sha_info, buffer, count);
}


