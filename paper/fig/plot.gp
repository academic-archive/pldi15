# set terminal x11

set terminal pdf font "Helvetica Light" size 15cm,10cm
set output "bound3d.pdf"

set grid
set view 64, 139, 1, 1.2
set ytics offset -2
set key left
set xyplane 0.1

inter(a,b) = a>=b ? 0 : b-a
bound(x,y) = 1.33 * inter(x,y) + 0.33 * inter(0,x)
splot \
  'plot.dat' ps 0.3 lt rgb "red" \
    title "measurements", \
  (bound(x,y)) lt rgb "blue" \
    title "inferred bound"
