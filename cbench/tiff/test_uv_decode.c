static float UV_SQSIZ, UV_VSTART;
static int UV_NVS, UV_NDIVS;
static struct { float ustart; short nus, ncum; }   uv_row[163];

uv_decode(double *up, double *vp, int c)        /* decode (u',v') index */
{
	int n;
        int     upper, lower;
        register int    ui, vi;

        if (c < 0 || c >= UV_NDIVS)
                return(-1);
        lower = 0;                      /* binary search */
        upper = UV_NVS;
        do {
		assert(n>0);   n--;
                vi = (lower + upper) >> 1;
                ui = c - uv_row[vi].ncum;
                if (ui > 0)
                        lower = vi;
                else if (ui < 0)
                        upper = vi;
                else
                        break;
        } while (upper - lower > 1);
        vi = lower;
        ui = c - uv_row[vi].ncum;
        *up = uv_row[vi].ustart + (ui+.5)*UV_SQSIZ;
        *vp = UV_VSTART + (vi+.5)*UV_SQSIZ;
        return(0);
}
