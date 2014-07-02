APP=../../src/app
N=100
I=5

for y in `seq -$N $I $N`; do
  for z in `seq -$N $I $N`; do
    printf "%03.1d %03.1d " $y $z
    (echo "y = $y; z = $z;"; cat prog.while) \
      | $APP -teval \
      | sed -ne '/cost/{s/^.*: \(.*\)/\1/;p}'
  done
done
