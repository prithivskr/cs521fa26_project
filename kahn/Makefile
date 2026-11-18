# Standalone Kahn-semantics proofs; needs only Rocq 9.1 and its standard library.
ROCQ ?= rocq
FLAGS = -Q . Kahn

.PHONY: all check clean
all: ChainReduceProof.vo

Spec.vo: Spec.v
	$(ROCQ) compile $(FLAGS) $<
Kahn.vo: Kahn.v Spec.vo
	$(ROCQ) compile $(FLAGS) $<
ChainReduce.vo: ChainReduce.v Kahn.vo
	$(ROCQ) compile $(FLAGS) $<
ChainReduceProof.vo: ChainReduceProof.v ChainReduce.vo
	$(ROCQ) compile $(FLAGS) $<

# Compile, then independently recheck the proof objects.
check: all
	$(ROCQ) check $(FLAGS) Kahn.Spec Kahn.Kahn Kahn.ChainReduce Kahn.ChainReduceProof

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
