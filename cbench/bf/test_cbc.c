typedef struct bf_key_st
 {
 unsigned long P[16 +2];
 unsigned long S[4*256];
 } BF_KEY;



void BF_encrypt(data,key,encrypt)
unsigned long *data;
BF_KEY *key;
int encrypt;
 {
 register unsigned long l,r,*p,*s;

 p=key->P;
 s= &(key->S[0]);
 l=data[0];
 r=data[1];

 if (encrypt)
  {
  l^=p[0];
  r^=p[ 1]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 2]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 3]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 4]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 5]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 6]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 7]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 8]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 9]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[10]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[11]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[12]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[13]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[14]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[15]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[16]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;






  r^=p[16 +1];
  }
 else
  {
  l^=p[16 +1];






  r^=p[16]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[15]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[14]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[13]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[12]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[11]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[10]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 9]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 8]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 7]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 6]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 5]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 4]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 3]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[ 2]; r^=((( s[ (l>>24L) ] + s[0x0100+((l>>16L)&0xff)])^ s[0x0200+((l>> 8L)&0xff)])+ s[0x0300+((l )&0xff)])&0xffffffff;;
  l^=p[ 1]; l^=((( s[ (r>>24L) ] + s[0x0100+((r>>16L)&0xff)])^ s[0x0200+((r>> 8L)&0xff)])+ s[0x0300+((r )&0xff)])&0xffffffff;;
  r^=p[0];
  }
 data[1]=l&0xffffffff;
 data[0]=r&0xffffffff;
 }
typedef struct bf_key_st
 {
 unsigned long P[16 +2];
 unsigned long S[4*256];
 } BF_KEY;



void BF_cbc_encrypt(in, out, length, ks, iv, encrypt)
unsigned char *in;
unsigned char *out;
long length;
BF_KEY *ks;
unsigned char *iv;
int encrypt;
 {
 register unsigned long tin0,tin1;
 register unsigned long tout0,tout1,xor0,xor1;
 register long l=length;
 unsigned long tin[2];

 if (encrypt)
  {
  (tout0 =((unsigned long)(*((iv)++)))<<24L, tout0|=((unsigned long)(*((iv)++)))<<16L, tout0|=((unsigned long)(*((iv)++)))<< 8L, tout0|=((unsigned long)(*((iv)++))));
  (tout1 =((unsigned long)(*((iv)++)))<<24L, tout1|=((unsigned long)(*((iv)++)))<<16L, tout1|=((unsigned long)(*((iv)++)))<< 8L, tout1|=((unsigned long)(*((iv)++))));
  iv-=8;
  for (l-=8; l>=0; l-=8)
   {
   (tin0 =((unsigned long)(*((in)++)))<<24L, tin0|=((unsigned long)(*((in)++)))<<16L, tin0|=((unsigned long)(*((in)++)))<< 8L, tin0|=((unsigned long)(*((in)++))));
   (tin1 =((unsigned long)(*((in)++)))<<24L, tin1|=((unsigned long)(*((in)++)))<<16L, tin1|=((unsigned long)(*((in)++)))<< 8L, tin1|=((unsigned long)(*((in)++))));
   tin0^=tout0;
   tin1^=tout1;
   tin[0]=tin0;
   tin[1]=tin1;
   BF_encrypt(tin,ks,1);
   tout0=tin[0];
   tout1=tin[1];
   (*((out)++)=(unsigned char)(((tout0)>>24L)&0xff), *((out)++)=(unsigned char)(((tout0)>>16L)&0xff), *((out)++)=(unsigned char)(((tout0)>> 8L)&0xff), *((out)++)=(unsigned char)(((tout0) )&0xff));
   (*((out)++)=(unsigned char)(((tout1)>>24L)&0xff), *((out)++)=(unsigned char)(((tout1)>>16L)&0xff), *((out)++)=(unsigned char)(((tout1)>> 8L)&0xff), *((out)++)=(unsigned char)(((tout1) )&0xff));
   }
  if (l != -8)
   {
   { in+=l+8; tin0=tin1=0; switch (l+8) { case 8: tin1 =((unsigned long)(*(--(in)))) ; case 7: tin1|=((unsigned long)(*(--(in))))<< 8; case 6: tin1|=((unsigned long)(*(--(in))))<<16; case 5: tin1|=((unsigned long)(*(--(in))))<<24; case 4: tin0 =((unsigned long)(*(--(in)))) ; case 3: tin0|=((unsigned long)(*(--(in))))<< 8; case 2: tin0|=((unsigned long)(*(--(in))))<<16; case 1: tin0|=((unsigned long)(*(--(in))))<<24; } };
   tin0^=tout0;
   tin1^=tout1;
   tin[0]=tin0;
   tin[1]=tin1;
   BF_encrypt(tin,ks,1);
   tout0=tin[0];
   tout1=tin[1];
   (*((out)++)=(unsigned char)(((tout0)>>24L)&0xff), *((out)++)=(unsigned char)(((tout0)>>16L)&0xff), *((out)++)=(unsigned char)(((tout0)>> 8L)&0xff), *((out)++)=(unsigned char)(((tout0) )&0xff));
   (*((out)++)=(unsigned char)(((tout1)>>24L)&0xff), *((out)++)=(unsigned char)(((tout1)>>16L)&0xff), *((out)++)=(unsigned char)(((tout1)>> 8L)&0xff), *((out)++)=(unsigned char)(((tout1) )&0xff));
   }
  (*((iv)++)=(unsigned char)(((tout0)>>24L)&0xff), *((iv)++)=(unsigned char)(((tout0)>>16L)&0xff), *((iv)++)=(unsigned char)(((tout0)>> 8L)&0xff), *((iv)++)=(unsigned char)(((tout0) )&0xff));
  (*((iv)++)=(unsigned char)(((tout1)>>24L)&0xff), *((iv)++)=(unsigned char)(((tout1)>>16L)&0xff), *((iv)++)=(unsigned char)(((tout1)>> 8L)&0xff), *((iv)++)=(unsigned char)(((tout1) )&0xff));
  }
 else
  {
  (xor0 =((unsigned long)(*((iv)++)))<<24L, xor0|=((unsigned long)(*((iv)++)))<<16L, xor0|=((unsigned long)(*((iv)++)))<< 8L, xor0|=((unsigned long)(*((iv)++))));
  (xor1 =((unsigned long)(*((iv)++)))<<24L, xor1|=((unsigned long)(*((iv)++)))<<16L, xor1|=((unsigned long)(*((iv)++)))<< 8L, xor1|=((unsigned long)(*((iv)++))));
  iv-=8;
  for (l-=8; l>=0; l-=8)
   {
   (tin0 =((unsigned long)(*((in)++)))<<24L, tin0|=((unsigned long)(*((in)++)))<<16L, tin0|=((unsigned long)(*((in)++)))<< 8L, tin0|=((unsigned long)(*((in)++))));
   (tin1 =((unsigned long)(*((in)++)))<<24L, tin1|=((unsigned long)(*((in)++)))<<16L, tin1|=((unsigned long)(*((in)++)))<< 8L, tin1|=((unsigned long)(*((in)++))));
   tin[0]=tin0;
   tin[1]=tin1;
   BF_encrypt(tin,ks,0);
   tout0=tin[0]^xor0;
   tout1=tin[1]^xor1;
   (*((out)++)=(unsigned char)(((tout0)>>24L)&0xff), *((out)++)=(unsigned char)(((tout0)>>16L)&0xff), *((out)++)=(unsigned char)(((tout0)>> 8L)&0xff), *((out)++)=(unsigned char)(((tout0) )&0xff));
   (*((out)++)=(unsigned char)(((tout1)>>24L)&0xff), *((out)++)=(unsigned char)(((tout1)>>16L)&0xff), *((out)++)=(unsigned char)(((tout1)>> 8L)&0xff), *((out)++)=(unsigned char)(((tout1) )&0xff));
   xor0=tin0;
   xor1=tin1;
   }
  if (l != -8)
   {
   (tin0 =((unsigned long)(*((in)++)))<<24L, tin0|=((unsigned long)(*((in)++)))<<16L, tin0|=((unsigned long)(*((in)++)))<< 8L, tin0|=((unsigned long)(*((in)++))));
   (tin1 =((unsigned long)(*((in)++)))<<24L, tin1|=((unsigned long)(*((in)++)))<<16L, tin1|=((unsigned long)(*((in)++)))<< 8L, tin1|=((unsigned long)(*((in)++))));
   tin[0]=tin0;
   tin[1]=tin1;
   BF_encrypt(tin,ks,0);
   tout0=tin[0]^xor0;
   tout1=tin[1]^xor1;
   { out+=l+8; switch (l+8) { case 8: *(--(out))=(unsigned char)(((tout1) )&0xff); case 7: *(--(out))=(unsigned char)(((tout1)>> 8)&0xff); case 6: *(--(out))=(unsigned char)(((tout1)>>16)&0xff); case 5: *(--(out))=(unsigned char)(((tout1)>>24)&0xff); case 4: *(--(out))=(unsigned char)(((tout0) )&0xff); case 3: *(--(out))=(unsigned char)(((tout0)>> 8)&0xff); case 2: *(--(out))=(unsigned char)(((tout0)>>16)&0xff); case 1: *(--(out))=(unsigned char)(((tout0)>>24)&0xff); } };
   xor0=tin0;
   xor1=tin1;
   }
  (*((iv)++)=(unsigned char)(((xor0)>>24L)&0xff), *((iv)++)=(unsigned char)(((xor0)>>16L)&0xff), *((iv)++)=(unsigned char)(((xor0)>> 8L)&0xff), *((iv)++)=(unsigned char)(((xor0) )&0xff));
  (*((iv)++)=(unsigned char)(((xor1)>>24L)&0xff), *((iv)++)=(unsigned char)(((xor1)>>16L)&0xff), *((iv)++)=(unsigned char)(((xor1)>> 8L)&0xff), *((iv)++)=(unsigned char)(((xor1) )&0xff));
  }
 tin0=tin1=tout0=tout1=xor0=xor1=0;
 tin[0]=tin[1]=0;
 }

void start() {
	unsigned char *in, *out;
	long length;
	BF_KEY *ks;
	unsigned char *iv;
	int encrypt;
	BF_cbc_encrypt(in, out, length, ks, iv, encrypt);
}
