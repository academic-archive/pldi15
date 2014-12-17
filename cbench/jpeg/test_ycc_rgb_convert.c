
typedef unsigned int JDIMENSION;
typedef long INT32;
typedef unsigned char JSAMPLE;
typedef JSAMPLE *JSAMPROW;
typedef JSAMPROW *JSAMPARRAY;
typedef JSAMPARRAY *JSAMPIMAGE;





typedef struct {
  /* struct jpeg_color_deconverter pub; */
  int * Cr_r_tab;
  int * Cb_b_tab;
  INT32 * Cr_g_tab;
  INT32 * Cb_g_tab;
} my_color_deconverter;
typedef my_color_deconverter * my_cconvert_ptr;


/* n is an auxiliary variable that is
   num_rows * num_cols
*/
int n;


static void
ycc_rgb_convert (/* j_decompress_ptr cinfo, */
   JSAMPIMAGE input_buf, JDIMENSION input_row,
   JSAMPARRAY output_buf, int num_rows)
{
  my_cconvert_ptr cconvert /* = (my_cconvert_ptr) cinfo->cconvert*/;
  register int y, cb, cr;
  register JSAMPROW outptr;
  register JSAMPROW inptr0, inptr1, inptr2;
  register JDIMENSION col;
  JDIMENSION num_cols /*= cinfo->output_width*/;

  register JSAMPLE * range_limit /*= cinfo->sample_range_limit*/;
  register int * Crrtab = cconvert->Cr_r_tab;
  register int * Cbbtab = cconvert->Cb_b_tab;
  register INT32 * Crgtab = cconvert->Cr_g_tab;
  register INT32 * Cbgtab = cconvert->Cb_g_tab;
 
  while (--num_rows >= 0) {
    inptr0 = input_buf[0][input_row];
    inptr1 = input_buf[1][input_row];
    inptr2 = input_buf[2][input_row];
    input_row++;
    outptr = *output_buf++;
    assert(n>0); n--;
    for (col = 0; col < num_cols; col++) {
      assert(n>0); n--;
      y = ((int) (inptr0[col]));
      cb = ((int) (inptr1[col]));
      cr = ((int) (inptr2[col]));

      outptr[0] = range_limit[y + Crrtab[cr]];
      outptr[1] = range_limit[y +
         ((int) ((Cbgtab[cb] + Crgtab[cr]) >> (16))
                 )];
      outptr[2] = range_limit[y + Cbbtab[cb]];
      outptr += 3;
    }
  }
}

void start() {  JSAMPIMAGE ib; JDIMENSION ir; JSAMPARRAY ob; int nr; ycc_rgb_convert(ib, ir, ob, nr); }
