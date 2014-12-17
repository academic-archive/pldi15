
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



void BF_cfb64_encrypt(in, out, length, schedule, ivec, num, encrypt)
unsigned char *in;
unsigned char *out;
long length;
BF_KEY *schedule;
unsigned char *ivec;
int *num;
int encrypt;
 {
 register unsigned long v0,v1,t;
 register long n= *num;
 register long l=length;
 unsigned long ti[2];
 unsigned char *iv,c,cc;

 iv=(unsigned char *)ivec;
 if (encrypt)
  {
  while (l-->0)
   {
   if (n == 0)
    {
    (v0 =((unsigned long)(*((iv)++)))<<24L, v0|=((unsigned long)(*((iv)++)))<<16L, v0|=((unsigned long)(*((iv)++)))<< 8L, v0|=((unsigned long)(*((iv)++)))); ti[0]=v0;
    (v1 =((unsigned long)(*((iv)++)))<<24L, v1|=((unsigned long)(*((iv)++)))<<16L, v1|=((unsigned long)(*((iv)++)))<< 8L, v1|=((unsigned long)(*((iv)++)))); ti[1]=v1;
    BF_encrypt((unsigned long *)ti,schedule,1);
    iv=(unsigned char *)ivec;
    t=ti[0]; (*((iv)++)=(unsigned char)(((t)>>24L)&0xff), *((iv)++)=(unsigned char)(((t)>>16L)&0xff), *((iv)++)=(unsigned char)(((t)>> 8L)&0xff), *((iv)++)=(unsigned char)(((t) )&0xff));
    t=ti[1]; (*((iv)++)=(unsigned char)(((t)>>24L)&0xff), *((iv)++)=(unsigned char)(((t)>>16L)&0xff), *((iv)++)=(unsigned char)(((t)>> 8L)&0xff), *((iv)++)=(unsigned char)(((t) )&0xff));
    iv=(unsigned char *)ivec;
    }
   c= *(in++)^iv[n];
   *(out++)=c;
   iv[n]=c;
   n=(n+1)&0x07;
   }
  }
 else
  {
  while (l-->0)
   {
   if (n == 0)
    {
    (v0 =((unsigned long)(*((iv)++)))<<24L, v0|=((unsigned long)(*((iv)++)))<<16L, v0|=((unsigned long)(*((iv)++)))<< 8L, v0|=((unsigned long)(*((iv)++)))); ti[0]=v0;
    (v1 =((unsigned long)(*((iv)++)))<<24L, v1|=((unsigned long)(*((iv)++)))<<16L, v1|=((unsigned long)(*((iv)++)))<< 8L, v1|=((unsigned long)(*((iv)++)))); ti[1]=v1;
    BF_encrypt((unsigned long *)ti,schedule,1);
    iv=(unsigned char *)ivec;
    t=ti[0]; (*((iv)++)=(unsigned char)(((t)>>24L)&0xff), *((iv)++)=(unsigned char)(((t)>>16L)&0xff), *((iv)++)=(unsigned char)(((t)>> 8L)&0xff), *((iv)++)=(unsigned char)(((t) )&0xff));
    t=ti[1]; (*((iv)++)=(unsigned char)(((t)>>24L)&0xff), *((iv)++)=(unsigned char)(((t)>>16L)&0xff), *((iv)++)=(unsigned char)(((t)>> 8L)&0xff), *((iv)++)=(unsigned char)(((t) )&0xff));
    iv=(unsigned char *)ivec;
    }
   cc= *(in++);
   c=iv[n];
   iv[n]=cc;
   *(out++)=c^cc;
   n=(n+1)&0x07;
   }
  }
 v0=v1=ti[0]=ti[1]=t=c=cc=0;
 *num=n;
 }

void start() {
	unsigned char *in, *out;
	long length;
	BF_KEY *schedule;
	unsigned char *ivec;
	int *num;
	int encrypt;
	BF_cfb64_encrypt(in, out, length, schedule, ivec, num, encrypt);
}
