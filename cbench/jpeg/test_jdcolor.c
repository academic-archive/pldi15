
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

static void
build_ycc_rgb_table (/* j_decompress_ptr cinfo */)
{
  my_cconvert_ptr cconvert /* = (my_cconvert_ptr) cinfo->cconvert*/;
  int i;
  INT32 x;
 

  /*
  cconvert->Cr_r_tab = (int *)
    (*cinfo->mem->alloc_small) ((j_common_ptr) cinfo, 1,
    (255 +1) * ((size_t) sizeof(int)));
  cconvert->Cb_b_tab = (int *)
    (*cinfo->mem->alloc_small) ((j_common_ptr) cinfo, 1,
    (255 +1) * ((size_t) sizeof(int)));
  cconvert->Cr_g_tab = (INT32 *)
    (*cinfo->mem->alloc_small) ((j_common_ptr) cinfo, 1,
    (255 +1) * ((size_t) sizeof(INT32)));
  cconvert->Cb_g_tab = (INT32 *)
    (*cinfo->mem->alloc_small) ((j_common_ptr) cinfo, 1,
    (255 +1) * ((size_t) sizeof(INT32)));
  */

  for (i = 0, x = -128; i < 256; i++, x++) {



    cconvert->Cr_r_tab[i] = (int)
      ((((INT32) ((1.40200) * (1L<<16) + 0.5)) * x + ((INT32) 1 << (16 -1))) >> (16));

    cconvert->Cb_b_tab[i] = (int)
      ((((INT32) ((1.77200) * (1L<<16) + 0.5)) * x + ((INT32) 1 << (16 -1))) >> (16));

    cconvert->Cr_g_tab[i] = (- ((INT32) ((0.71414) * (1L<<16) + 0.5))) * x;


    cconvert->Cb_g_tab[i] = (- ((INT32) ((0.34414) * (1L<<16) + 0.5))) * x + ((INT32) 1 << (16 -1));
  }
}

void start() { build_ycc_rgb_table(); }

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
    for (col = 0; col < num_cols; col++) {
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

static void
null_convert (/* j_decompress_ptr cinfo, */
       JSAMPIMAGE input_buf, JDIMENSION input_row,
       JSAMPARRAY output_buf, int num_rows)
{
  register JSAMPROW inptr, outptr;
  register JDIMENSION count;
  register int num_components /* = cinfo->num_components */;
  JDIMENSION num_cols /* = cinfo->output_width */;
  int ci;

  while (--num_rows >= 0) {
    for (ci = 0; ci < num_components; ci++) {
      inptr = input_buf[ci][input_row];
      outptr = output_buf[0] + ci;
      for (count = num_cols; count > 0; count--) {
 *outptr = *inptr++;
 outptr += num_components;
      }
    }
    input_row++;
    output_buf++;
  }
}

static void
ycck_cmyk_convert (/* j_decompress_ptr cinfo, */
     JSAMPIMAGE input_buf, JDIMENSION input_row,
     JSAMPARRAY output_buf, int num_rows)
{
  my_cconvert_ptr cconvert /* = (my_cconvert_ptr) cinfo->cconvert */;
  register int y, cb, cr;
  register JSAMPROW outptr;
  register JSAMPROW inptr0, inptr1, inptr2, inptr3;
  register JDIMENSION col;
  JDIMENSION num_cols /* = cinfo->output_width */;

  register JSAMPLE * range_limit /* = cinfo->sample_range_limit */;
  register int * Crrtab = cconvert->Cr_r_tab;
  register int * Cbbtab = cconvert->Cb_b_tab;
  register INT32 * Crgtab = cconvert->Cr_g_tab;
  register INT32 * Cbgtab = cconvert->Cb_g_tab;
 

  while (--num_rows >= 0) {
    inptr0 = input_buf[0][input_row];
    inptr1 = input_buf[1][input_row];
    inptr2 = input_buf[2][input_row];
    inptr3 = input_buf[3][input_row];
    input_row++;
    outptr = *output_buf++;
    for (col = 0; col < num_cols; col++) {
      y = ((int) (inptr0[col]));
      cb = ((int) (inptr1[col]));
      cr = ((int) (inptr2[col]));

      outptr[0] = range_limit[255 - (y + Crrtab[cr])];
      outptr[1] = range_limit[255 - (y +
         ((int) ((Cbgtab[cb] + Crgtab[cr]) >> (16))
                 ))];
      outptr[2] = range_limit[255 - (y + Cbbtab[cb])];

      outptr[3] = inptr3[col];
      outptr += 4;
    }
  }
}

