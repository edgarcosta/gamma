INC=/data/local/include
LIB=/data/local/lib

g: g.c
	gcc -O -I$(INC) -I$(INC)/flint -o g g.c $(LIB)/libarb.a $(LIB)/libflint.a $(LIB)/libmpfr.a $(LIB)/libgmp.a -lm -lpthread
