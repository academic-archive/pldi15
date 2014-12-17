
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
