all : u0.vo u1.vo u2.vo
	coqc u01
	coqc u12


u0.vo : u0.v
	coqc u0

u1.vo : u0.v
	cp u0.v u1.v
	coqc u1

u2.vo : u0.v
	cp u0.v u2.v
	coqc u2

