
struct mad_bitptr {
  unsigned char const *byte;
  unsigned short cache;
  unsigned short left;
};








unsigned long mad_bit_read(struct mad_bitptr *bitptr, unsigned int len)
{
  unsigned left;
  register unsigned long value;

  if (bitptr->left == 8)
    bitptr->cache = *bitptr->byte;

  if (len < bitptr->left) {
    value = (bitptr->cache & ((1 << bitptr->left) - 1)) >>
      (bitptr->left - len);
    bitptr->left -= len;

    return value;
  }



  value = bitptr->cache & ((1 << bitptr->left) - 1);
  left = bitptr->left;
  assert(left >= 0);
  len -= left;

  bitptr->byte++;
  bitptr->left = 8;



  while (len >= 8) {
    value = (value << 8) | *bitptr->byte++;
    len -= 8;
  }

  if (len > 0) {
    bitptr->cache = *bitptr->byte;

    value = (value << len) | (bitptr->cache >> (8 - len));
    bitptr->left -= len;
  }

  return value;
}

void start()
{
	struct mad_bitptr bitptr;
	unsigned int len;
	unsigned short init;
	mad_bit_read(&bitptr, len);
	// mad_bit_crc(bitptr, len, init);
}
