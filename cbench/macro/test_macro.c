void memmove(void *dst, void *src, int n) {
	char *d = dst, *s = src;
	while (n > 0) {
		// *d = *s; // unsupported heap assignment
		d = d+1;
		s = s+1;
		n = n-1;
	}
}

void memcpy(void *dst, void *src, int n) {
	char *d = dst, *s = src;
	while (n > 0) {
		// *d = *s; // unsupported heap assignment
		d = d+1;
		s = s+1;
		n = n-1;
	}
}

void memset(void *p, int i, unsigned n) {
	char *c = p;
	while (n > 0) {
		// *c = i; // unsupported heap assignment
		c = c+1;
		n = n-1;
	}
}

typedef unsigned char boolean;
typedef unsigned char byte;
typedef byte *byteptr;
typedef char *string;
typedef unsigned short word16;



typedef unsigned long word32;

struct IdeaCfbContext {
 byte oldcipher[8];
 byte iv[8];
 word16 key[(6*8 +4)];
 int bufleft;
};

struct IdeaRandContext {
 byte outbuf[8];
 word16 key[(6*8 +4)];
 int bufleft;
 byte internalbuf[8];
};

typedef word16 uint16;

 static uint16
 mulInv(uint16 x)
{
    uint16 t0, t1;
    uint16 q, y;
    int X;

    if (x <= 1)
 return x;
    t1 = 0x10001L / x;
    y = 0x10001L % x;
    if (y == 1)
 return (1 - t1);
    t0 = 1;
    X = 32;
    assert(X>0);
    do {
 q = x / y;
 x = x % y;
 t0 += q * t1;
 if (x == 1)
     return t0;
 q = y / x;
 y = y % x;
 t1 += q * t0;
 if (X <= 0) break;
 X--;
    } while (y != 1);
    return (1 - t1);
}




static void ideaExpandKey(byte const *userkey, word16 * EK)
{
    int i, j;

    for (j = 0; j < 8; j++) {
 EK[j] = (userkey[0] << 8) + userkey[1];
 userkey += 2;
    }
    for (i = 0; j < (6*8 +4); j++) {
 i++;
 EK[i + 7] = EK[i & 7] << 9 | EK[i + 1 & 7] >> 7;
 EK += i & 8;
 i &= 7;
    }
}






static void  ideaInvertKey  (word16 const *EK, word16 DK[(6*8 +4)])
{
    int i;
    uint16 t1, t2, t3, x;
    word16 temp[(6*8 +4)];
    word16 *p = temp + (6*8 +4);

    x = *EK++;
    t1 = mulInv(x);
    t2 = -*EK++;
    t3 = -*EK++;
    x = *EK++;
    *--p = mulInv(x);
    *--p = t3;
    *--p = t2;
    *--p = t1;

    for (i = 0; i < 8 - 1; i++) {
 t1 = *EK++;
 *--p = *EK++;
 *--p = t1;

 x = *EK++;
 t1 = mulInv(x);
 t2 = -*EK++;
 t3 = -*EK++;
 x = *EK++;
 *--p = mulInv(x);
 *--p = t2;
 *--p = t3;
 *--p = t1;
    }
    t1 = *EK++;
    *--p = *EK++;
    *--p = t1;

    x = *EK++;
    t1 = mulInv(x);
    t2 = -*EK++;
    t3 = -*EK++;
    x = *EK++;
    *--p = mulInv(x);
    *--p = t3;
    *--p = t2;
    *--p = t1;

    memcpy(DK, temp, 104/*sizeof(temp)*/);
    memset( (void *)&(temp), 0, 104/*sizeof(temp)*/ );
}
static void ideaCipher(byte const inbuf[8], byte outbuf[8],
         word16 const *key)
{
    register uint16 x1, x2, x3, x4, s2, s3;
    word16 *in, *out;

    register uint16 t16;
    register word32 t32;

    int r = 8;

    in = (word16 *) inbuf;
    x1 = *in++;
    x2 = *in++;
    x3 = *in++;
    x4 = *in;

    x1 = (x1 >> 8) | (x1 << 8);
    x2 = (x2 >> 8) | (x2 << 8);
    x3 = (x3 >> 8) | (x3 << 8);
    x4 = (x4 >> 8) | (x4 << 8);
    do {

 ((t16 = (*key++)) ? (x1=(x1)) ? t32 = (word32)x1*t16, x1 = (t32), t16 = t32>>16, x1 = (x1-t16)+(x1<t16) : (x1 = 1-t16) : (x1 = 1-x1));
 x2 += *key++;
 x3 += *key++;
 ((t16 = (*key++)) ? (x4=(x4)) ? t32 = (word32)x4*t16, x4 = (t32), t16 = t32>>16, x4 = (x4-t16)+(x4<t16) : (x4 = 1-t16) : (x4 = 1-x4));

 s3 = x3;
 x3 ^= x1;
 ((t16 = (*key++)) ? (x3=(x3)) ? t32 = (word32)x3*t16, x3 = (t32), t16 = t32>>16, x3 = (x3-t16)+(x3<t16) : (x3 = 1-t16) : (x3 = 1-x3));
 s2 = x2;
 x2 ^= x4;
 x2 += x3;
 ((t16 = (*key++)) ? (x2=(x2)) ? t32 = (word32)x2*t16, x2 = (t32), t16 = t32>>16, x2 = (x2-t16)+(x2<t16) : (x2 = 1-t16) : (x2 = 1-x2));
 x3 += x2;

 x1 ^= x2;
 x4 ^= x3;

 x2 ^= s3;
 x3 ^= s2;
    assert(r>0);
    } while (--r > 0);
    ((t16 = (*key++)) ? (x1=(x1)) ? t32 = (word32)x1*t16, x1 = (t32), t16 = t32>>16, x1 = (x1-t16)+(x1<t16) : (x1 = 1-t16) : (x1 = 1-x1));
    x3 += *key++;
    x2 += *key++;
    ((t16 = (*key)) ? (x4=(x4)) ? t32 = (word32)x4*t16, x4 = (t32), t16 = t32>>16, x4 = (x4-t16)+(x4<t16) : (x4 = 1-t16) : (x4 = 1-x4));

    out = (word16 *) outbuf;






    x1 = (x1);
    x2 = (x2);
    x3 = (x3);
    x4 = (x4);
    *out++ = (x1 >> 8) | (x1 << 8);
    *out++ = (x3 >> 8) | (x3 << 8);
    *out++ = (x2 >> 8) | (x2 << 8);
    *out = (x4 >> 8) | (x4 << 8);

}
void ideaCfbReinit(struct IdeaCfbContext *context, byte const *iv)
{
    if (iv)
 memcpy(context->iv, iv, 8);
    else
 memset( context->iv, 0, 8 );
    context->bufleft = 0;
}

void ideaCfbInit(struct IdeaCfbContext *context, byte const key[16])
{
    ideaExpandKey(key, context->key);
    ideaCfbReinit(context, 0);
}

void ideaCfbDestroy(struct IdeaCfbContext *context)
{
    // memset( (void *)&(*context), 0, sizeof(*context) );
}
void ideaCfbSync(struct IdeaCfbContext *context)
{
    int n;
    int bufleft = context->bufleft;

    assert(bufleft <= 8);
    if (bufleft > 0) {
 n = 8;
 n -= bufleft;
 memmove(context->iv + bufleft, context->iv, n /*8 - bufleft*/);
 memcpy(context->iv, context->oldcipher + 8 - bufleft, bufleft);
 context->bufleft = 0;
    }
}






void ideaCfbEncrypt(struct IdeaCfbContext *context, byte const *src,
      byte * dest, int count)
{
    int bufleft = context->bufleft;
    byte *bufptr = context->iv + 8 - bufleft;


    assert(bufleft >= 0);
    assert(bufleft <= 8);

    if (count <= bufleft) {
 context->bufleft = bufleft - count;
 while (count-->0) {
     *dest++ = *bufptr++ ^= *src++;
 }
 return;
    }

    count -= bufleft;
    while (bufleft-->0) {
 *dest++ = (*bufptr++ ^= *src++);
    }

    while (count > 8) {
 bufptr = context->iv;
 memcpy(context->oldcipher, bufptr, 8);
 ideaCipher(bufptr, bufptr, context->key);
 bufleft = 8;
 count -= 8;
 do {
     *dest++ = (*bufptr++ ^= *src++);
 } while (--bufleft>0);
    }

    bufptr = context->iv;
    memcpy(context->oldcipher, bufptr, 8);
    ideaCipher(bufptr, bufptr, context->key);
    context->bufleft = 8 - count;
    do {
 *dest++ = (*bufptr++ ^= *src++);
    } while (--count>0);
}




void ideaCfbDecrypt(struct IdeaCfbContext *context, byte const *src,
      byte * dest, int count)
{
    int bufleft = context->bufleft;
    static byte *bufptr;
    byte t;

    assert(bufleft >= 0);
    assert(bufleft <= 8);

    bufptr = context->iv + (8 - bufleft);
    if (count <= bufleft) {
 context->bufleft = bufleft - count;
 while (count-->0) {
     t = *bufptr;
     *dest++ = t ^ (*bufptr++ = *src++);
 }
 return;
    }
    count -= bufleft;
    while (bufleft-->0) {
 t = *bufptr;
 *dest++ = t ^ (*bufptr++ = *src++);
    }
    while (count > 8) {
 bufptr = context->iv;
 memcpy(context->oldcipher, bufptr, 8);
 ideaCipher(bufptr, bufptr, context->key);
 bufleft = 8;
 count -= 8;
 do {
     t = *bufptr;
     *dest++ = t ^ (*bufptr++ = *src++);
 } while (--bufleft>0);
    }
    bufptr = context->iv;
    memcpy(context->oldcipher, bufptr, 8);
    ideaCipher(bufptr, bufptr, context->key);
    context->bufleft = 8 - count;
    do {
 t = *bufptr;
 *dest++ = t ^ (*bufptr++ = *src++);
    } while (--count>0);
}
/*
 * This code implements the MD5 message-digest algorithm.
 * The algorithm is due to Ron Rivest.  This code was
 * written by Colin Plumb in 1993, no copyright is claimed.
 * This code is in the public domain; do with it what you wish.
 *
 * Equivalent code is available from RSA Data Security, Inc.
 * This code has been tested against that, and is equivalent,
 * except that you don't need to include two pages of legalese
 * with every copy.
 *
 * To compute the message digest of a chunk of bytes, declare an
 * MD5Context structure, pass it to MD5Init, call MD5Update as
 * needed on buffers full of bytes, and then call MD5Final, which
 * will fill a supplied 16-byte array with the digest.
 */

/* Valid on both 32 and 64 bits intel architectures. */
typedef unsigned int uint32;

/* Global MD5 module state. */
struct MD5Context {
	uint32 buf[4];
	uint32 bits[2];
	unsigned char in[64];
} ctx;


/*
 * Start MD5 accumulation.  Set bit count to 0 and buffer to mysterious
 * initialization constants.
 */
void MD5Init()
{
    ctx.buf[0] = 0x67452301;
    ctx.buf[1] = 0xefcdab89;
    ctx.buf[2] = 0x98badcfe;
    ctx.buf[3] = 0x10325476;

    ctx.bits[0] = 0;
    ctx.bits[1] = 0;
}

/*
 * Update context to reflect the concatenation of another buffer full
 * of bytes.
 */
void MD5Update(unsigned char const *buf, int len)
{
    int t;

    /* Update bitcount */

    t = ctx.bits[0];
    ctx.bits[0] = t + ((uint32) len << 3);
    if (ctx.bits[0] < t)
	ctx.bits[1]++;		/* Carry from low to high */
    ctx.bits[1] = ctx.bits[1] + (len >> 29);

    t = (t >> 3) & 0x3f;	/* Bytes already in shsInfo->data */

    /* Handle any leading odd-sized chunks */

    if (t) {
	unsigned char *p = (unsigned char *) ctx.in + t;
        assert(t < 64);  /* necessary because of the bitwise operations */
        assert(t >= 0);

	t = 64 - t;
	if (len < t) {
	    memcpy(p, buf, len);
	    return;
	}
	memcpy(p, buf, t);
	MD5Transform(ctx.buf, (uint32 *) ctx.in);
	buf = buf + t;
	len = len - t;
    }
    /* Process data in 64-byte chunks */

    while (len >= 64) {
	len = len - 64;
	memcpy(ctx.in, buf, 64);
	MD5Transform(ctx.buf, (uint32 *) ctx.in);
	buf = buf + 64;
    }

    /* Handle any remaining bytes of data. */

    memcpy(ctx.in, buf, len);
}

/*
 * Final wrapup - pad to 64-byte boundary with the bit pattern
 * 1 0* (64-bit count of bits processed, MSB-first)
 */
void MD5Final(unsigned char digest[16])
{
    unsigned count;
    unsigned char *p;

    /* Compute number of bytes mod 64 */
    count = (ctx.bits[0] >> 3) & 0x3F;
    assert(count <= 64);  /* necessary because of the bitwise operations */
    assert(count >= 0);

    /* Set the first char of padding to 0x80.  This is safe since there is
       always at least one byte free */
    p = ctx.in + count;
    // *p = 0x80;
    p = p+1;

    /* Bytes of padding needed to make 64 bytes */
    count = 64 - 1 - count;

    /* Pad out to 56 mod 64 */
    if (count < 8) {
	/* Two lots of padding:  Pad the first block to 64 bytes */
	memset(p, 0, count);
	MD5Transform((uint32 *) ctx.in);

	/* Now fill the next block with 56 bytes */
	memset(ctx.in, 0, 56);
    } else {
	/* Pad block to 56 bytes */
	count -= 8;
	memset(p, 0, count);
    }

    /* Append length in bits and transform */
    // Poor style, should be using shifts and masks.
    // ((uint32 *) ctx.in)[14] = ctx.bits[0];
    // ((uint32 *) ctx.in)[15] = ctx.bits[1];

    MD5Transform(ctx.buf, (uint32 *) ctx.in);
    memcpy(digest, ctx.buf, 16);
}

/*
 * The core of the MD5 algorithm, this alters an existing MD5 hash to
 * reflect the addition of 16 longwords of new data.  MD5Update blocks
 * the data and converts bytes into longwords for this routine.
 */
void MD5Transform(uint32 const in[16])
{
    register uint32 __attribute__((notrack)) a, b, c, d;

    a = ctx.buf[0];
    b = ctx.buf[1];
    c = ctx.buf[2];
    d = ctx.buf[3];

    { a = a + ((d ^ (b & (c ^ d))) + in[0] + 0xd76aa478); a = a<<7 | a>>(32-7); a = a + b; };
    { d = d + ((c ^ (a & (b ^ c))) + in[1] + 0xe8c7b756); d = d<<12 | d>>(32-12); d = d + a; };
    { c = c + ((b ^ (d & (a ^ b))) + in[2] + 0x242070db); c = c<<17 | c>>(32-17); c = c + d; };
    { b = b + ((a ^ (c & (d ^ a))) + in[3] + 0xc1bdceee); b = b<<22 | b>>(32-22); b = b + c; };
    { a = a + ((d ^ (b & (c ^ d))) + in[4] + 0xf57c0faf); a = a<<7 | a>>(32-7); a = a + b; };
    { d = d + ((c ^ (a & (b ^ c))) + in[5] + 0x4787c62a); d = d<<12 | d>>(32-12); d = d + a; };
    { c = c + ((b ^ (d & (a ^ b))) + in[6] + 0xa8304613); c = c<<17 | c>>(32-17); c = c + d; };
    { b = b + ((a ^ (c & (d ^ a))) + in[7] + 0xfd469501); b = b<<22 | b>>(32-22); b = b + c; };
    { a = a + ((d ^ (b & (c ^ d))) + in[8] + 0x698098d8); a = a<<7 | a>>(32-7); a = a + b; };
    { d = d + ((c ^ (a & (b ^ c))) + in[9] + 0x8b44f7af); d = d<<12 | d>>(32-12); d = d + a; };
    { c = c + ((b ^ (d & (a ^ b))) + in[10] + 0xffff5bb1); c = c<<17 | c>>(32-17); c = c + d; };
    { b = b + ((a ^ (c & (d ^ a))) + in[11] + 0x895cd7be); b = b<<22 | b>>(32-22); b = b + c; };
    { a = a + ((d ^ (b & (c ^ d))) + in[12] + 0x6b901122); a = a<<7 | a>>(32-7); a = a + b; };
    { d = d + ((c ^ (a & (b ^ c))) + in[13] + 0xfd987193); d = d<<12 | d>>(32-12); d = d + a; };
    { c = c + ((b ^ (d & (a ^ b))) + in[14] + 0xa679438e); c = c<<17 | c>>(32-17); c = c + d; };
    { b = b + ((a ^ (c & (d ^ a))) + in[15] + 0x49b40821); b = b<<22 | b>>(32-22); b = b + c; };

    { a = a + ((c ^ (d & (b ^ c))) + in[1] + 0xf61e2562); a = a<<5 | a>>(32-5); a = a + b; };
    { d = d + ((b ^ (c & (a ^ b))) + in[6] + 0xc040b340); d = d<<9 | d>>(32-9); d = d + a; };
    { c = c + ((a ^ (b & (d ^ a))) + in[11] + 0x265e5a51); c = c<<14 | c>>(32-14); c = c + d; };
    { b = b + ((d ^ (a & (c ^ d))) + in[0] + 0xe9b6c7aa); b = b<<20 | b>>(32-20); b = b + c; };
    { a = a + ((c ^ (d & (b ^ c))) + in[5] + 0xd62f105d); a = a<<5 | a>>(32-5); a = a + b; };
    { d = d + ((b ^ (c & (a ^ b))) + in[10] + 0x02441453); d = d<<9 | d>>(32-9); d = d + a; };
    { c = c + ((a ^ (b & (d ^ a))) + in[15] + 0xd8a1e681); c = c<<14 | c>>(32-14); c = c + d; };
    { b = b + ((d ^ (a & (c ^ d))) + in[4] + 0xe7d3fbc8); b = b<<20 | b>>(32-20); b = b + c; };
    { a = a + ((c ^ (d & (b ^ c))) + in[9] + 0x21e1cde6); a = a<<5 | a>>(32-5); a = a + b; };
    { d = d + ((b ^ (c & (a ^ b))) + in[14] + 0xc33707d6); d = d<<9 | d>>(32-9); d = d + a; };
    { c = c + ((a ^ (b & (d ^ a))) + in[3] + 0xf4d50d87); c = c<<14 | c>>(32-14); c = c + d; };
    { b = b + ((d ^ (a & (c ^ d))) + in[8] + 0x455a14ed); b = b<<20 | b>>(32-20); b = b + c; };
    { a = a + ((c ^ (d & (b ^ c))) + in[13] + 0xa9e3e905); a = a<<5 | a>>(32-5); a = a + b; };
    { d = d + ((b ^ (c & (a ^ b))) + in[2] + 0xfcefa3f8); d = d<<9 | d>>(32-9); d = d + a; };
    { c = c + ((a ^ (b & (d ^ a))) + in[7] + 0x676f02d9); c = c<<14 | c>>(32-14); c = c + d; };
    { b = b + ((d ^ (a & (c ^ d))) + in[12] + 0x8d2a4c8a); b = b<<20 | b>>(32-20); b = b + c; };

    { a = a + ((b ^ c ^ d) + in[5] + 0xfffa3942); a = a<<4 | a>>(32-4); a = a + b; };
    { d = d + ((a ^ b ^ c) + in[8] + 0x8771f681); d = d<<11 | d>>(32-11); d = d + a; };
    { c = c + ((d ^ a ^ b) + in[11] + 0x6d9d6122); c = c<<16 | c>>(32-16); c = c + d; };
    { b = b + ((c ^ d ^ a) + in[14] + 0xfde5380c); b = b<<23 | b>>(32-23); b = b + c; };
    { a = a + ((b ^ c ^ d) + in[1] + 0xa4beea44); a = a<<4 | a>>(32-4); a = a + b; };
    { d = d + ((a ^ b ^ c) + in[4] + 0x4bdecfa9); d = d<<11 | d>>(32-11); d = d + a; };
    { c = c + ((d ^ a ^ b) + in[7] + 0xf6bb4b60); c = c<<16 | c>>(32-16); c = c + d; };
    { b = b + ((c ^ d ^ a) + in[10] + 0xbebfbc70); b = b<<23 | b>>(32-23); b = b + c; };
    { a = a + ((b ^ c ^ d) + in[13] + 0x289b7ec6); a = a<<4 | a>>(32-4); a = a + b; };
    { d = d + ((a ^ b ^ c) + in[0] + 0xeaa127fa); d = d<<11 | d>>(32-11); d = d + a; };
    { c = c + ((d ^ a ^ b) + in[3] + 0xd4ef3085); c = c<<16 | c>>(32-16); c = c + d; };
    { b = b + ((c ^ d ^ a) + in[6] + 0x04881d05); b = b<<23 | b>>(32-23); b = b + c; };
    { a = a + ((b ^ c ^ d) + in[9] + 0xd9d4d039); a = a<<4 | a>>(32-4); a = a + b; };
    { d = d + ((a ^ b ^ c) + in[12] + 0xe6db99e5); d = d<<11 | d>>(32-11); d = d + a; };
    { c = c + ((d ^ a ^ b) + in[15] + 0x1fa27cf8); c = c<<16 | c>>(32-16); c = c + d; };
    { b = b + ((c ^ d ^ a) + in[2] + 0xc4ac5665); b = b<<23 | b>>(32-23); b = b + c; };

    { a = a + ((c ^ (b | ~d)) + in[0] + 0xf4292244); a = a<<6 | a>>(32-6); a = a + b; };
    { d = d + ((b ^ (a | ~c)) + in[7] + 0x432aff97); d = d<<10 | d>>(32-10); d = d + a; };
    { c = c + ((a ^ (d | ~b)) + in[14] + 0xab9423a7); c = c<<15 | c>>(32-15); c = c + d; };
    { b = b + ((d ^ (c | ~a)) + in[5] + 0xfc93a039); b = b<<21 | b>>(32-21); b = b + c; };
    { a = a + ((c ^ (b | ~d)) + in[12] + 0x655b59c3); a = a<<6 | a>>(32-6); a = a + b; };
    { d = d + ((b ^ (a | ~c)) + in[3] + 0x8f0ccc92); d = d<<10 | d>>(32-10); d = d + a; };
    { c = c + ((a ^ (d | ~b)) + in[10] + 0xffeff47d); c = c<<15 | c>>(32-15); c = c + d; };
    { b = b + ((d ^ (c | ~a)) + in[1] + 0x85845dd1); b = b<<21 | b>>(32-21); b = b + c; };
    { a = a + ((c ^ (b | ~d)) + in[8] + 0x6fa87e4f); a = a<<6 | a>>(32-6); a = a + b; };
    { d = d + ((b ^ (a | ~c)) + in[15] + 0xfe2ce6e0); d = d<<10 | d>>(32-10); d = d + a; };
    { c = c + ((a ^ (d | ~b)) + in[6] + 0xa3014314); c = c<<15 | c>>(32-15); c = c + d; };
    { b = b + ((d ^ (c | ~a)) + in[13] + 0x4e0811a1); b = b<<21 | b>>(32-21); b = b + c; };
    { a = a + ((c ^ (b | ~d)) + in[4] + 0xf7537e82); a = a<<6 | a>>(32-6); a = a + b; };
    { d = d + ((b ^ (a | ~c)) + in[11] + 0xbd3af235); d = d<<10 | d>>(32-10); d = d + a; };
    { c = c + ((a ^ (d | ~b)) + in[2] + 0x2ad7d2bb); c = c<<15 | c>>(32-15); c = c + d; };
    { b = b + ((d ^ (c | ~a)) + in[9] + 0xeb86d391); b = b<<21 | b>>(32-21); b = b + c; };

    ctx.buf[0] += a;
    ctx.buf[1] += b;
    ctx.buf[2] += c;
    ctx.buf[3] += d;
}




int start(byte key[16], char buf[], int len) {
	struct IdeaCfbContext ctx;
	char *obuf;
	char digest[16];

	/* obuf = malloc(len); */

	ideaCfbInit(&ctx, key);
	ideaCfbDecrypt(&ctx, buf, obuf, len);

	MD5Init();
	MD5Update(obuf, len);
	MD5Final(digest);

	return 0;
}

/*

== Function sizes:

ideaCfbDecrypt        44
ideaCipher            66
memcpy                9
ideaCfbInit           5
ideaCfbReinit         8
memset                9
ideaExpandKey         15
MD5Final              41
MD5Transform          82
MD5Update             44
MD5Init               10


== Test results:

Run 1: MD5 (495 lines) (1.135 sec)
Run 2: IDEA (240 lines) (4.632 sec)
Run 3: IDEA & MD5 (735 lines) (6.721 sec)

*/
