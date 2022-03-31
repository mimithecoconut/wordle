default: compile

NAME = midterm
OCAMLC = ocamlfind ocamlc

all: compile test

compile: clean
	${OCAMLC} -c ${NAME}.mli ${NAME}.ml

test:
	${OCAMLC} -o tests_${NAME} \
	 -package ounit2 -linkpkg \
	  ${NAME}.cmo tests_${NAME}.ml
	./tests_${NAME}

clean:
	rm -f *.cm* *.log *.cache tests_${NAME}
