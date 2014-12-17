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
# 272 "idea.c"
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
# 437 "idea.c"
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
# 482 "idea.c"
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


void start() {
  struct IdeaCfbContext *context;
  byte *src, *dest;
  int count;
  ideaCfbEncrypt(context, src, dest, count);
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
