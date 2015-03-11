verbatimtex \input 9point \ninepoint etex

beginfig(1);
pair pl; pl = (0,0);
pair pr; pr = (7cm,0);
pair sh; sh = (0, 1cm);
pair px;
pair pxx;

draw pl--pr;
px  := 1/4[pl,pr];
pxx := 2/4[pl,pr];
drawarrow px{dir(-45)}..pxx;
dotlabel.top(btex $x$ etex, px);
dotlabel.top(btex $x{+}y$ etex, pxx);
dotlabel.top(btex $z$ etex, 3/4[pl,pr]);

pl := pl + sh;
pr := pr + sh;
draw pl--pr;
px  := 3/8[pl,pr];
pxx := 5/8[pl,pr];
drawarrow px{dir(-45)}..pxx;
dotlabel.top(btex $x$ etex, px);
dotlabel.top(btex $z$ etex, 2/4[pl,pr]);
dotlabel.top(btex $x{+}y$ etex, pxx);

pl := pl + sh;
pr := pr + sh;
draw pl--pr;
px  := 2/4[pl,pr];
pxx := 3/4[pl,pr];
drawarrow px{dir(-45)}..pxx;
dotlabel.top(btex $z$ etex,  1/4[pl,pr]);
dotlabel.top(btex $x$ etex,  px);
dotlabel.top(btex $x{+}y$ etex, pxx);
endfig;

end;
