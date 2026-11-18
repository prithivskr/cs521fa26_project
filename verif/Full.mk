# Companion to the user's rocq-generated Makefile; does not replace it.
ROCQ ?= rocq
OCAMLC ?= ocamlc
PYTHON ?= .venv/bin/python
FLAGS = -Q . SpatialCSL
.PHONY: all check emit lower test numeric-test chain-emit chain
all: check
SpadaIR.vo: SpadaIR.v
	$(ROCQ) compile $(FLAGS) $<
SpadaExamples.vo: SpadaExamples.v SpadaIR.vo
	$(ROCQ) compile $(FLAGS) $<
emit: SpadaExamples.vo SpadaKernelProofs.vo SpadaRoutingExamples.vo SpadaExtract.v spada_emit.ml
	mkdir -p _build
	$(ROCQ) compile $(FLAGS) SpadaExtract.v
	$(OCAMLC) -c -o _build/spada_generated.cmi _build/spada_generated.mli
	$(OCAMLC) -I _build -c -o _build/spada_generated.cmo _build/spada_generated.ml
	$(OCAMLC) -I _build -c -o _build/spada_emit.cmo spada_emit.ml
	$(OCAMLC) -I _build -o _build/spada_emit _build/spada_generated.cmo _build/spada_emit.cmo
	./_build/spada_emit generated-spada
lower: emit
	$(PYTHON) spada_bridge.py generated-spada/manual-ping.json --output generated-spada/manual-ping
	$(PYTHON) spada_bridge.py generated-spada/ping.json --output generated-spada/ping
	$(PYTHON) spada_bridge.py generated-spada/multicast.json --output generated-spada/multicast
	$(PYTHON) spada_bridge.py generated-spada/pipeline.json --output generated-spada/pipeline
	$(PYTHON) spada_bridge.py generated-spada/host.json --output generated-spada/host
	$(PYTHON) spada_bridge.py generated-spada/epochs.json --output generated-spada/epochs
	$(PYTHON) spada_bridge.py generated-spada/meta.json --output generated-spada/meta
	$(PYTHON) spada_bridge.py generated-spada/bounded.json --output generated-spada/bounded
	$(PYTHON) spada_bridge.py generated-spada/external.json --output generated-spada/external
test: emit
	$(PYTHON) -m unittest -v test_spada_bridge

SpadaSemantics.vo: SpadaSemantics.v SpadaIR.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaArithmetic.vo: SpadaArithmetic.v SpadaSemantics.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaEquivalence.vo: SpadaEquivalence.v SpadaSemantics.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaElaboration.vo: SpadaElaboration.v SpadaEquivalence.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaProgramProofs.vo: SpadaProgramProofs.v SpadaExamples.vo SpadaArithmetic.vo SpadaElaboration.vo
	$(ROCQ) compile $(FLAGS) $<
check: SummaLocalProof.vo SpadaRoutingExamples.vo SpadaKernelProofs.vo SpadaExamples.vo SpadaArithmetic.vo SpadaElaboration.vo SpadaProgramProofs.vo
	$(ROCQ) check $(FLAGS) SpatialCSL.SpadaIR SpatialCSL.SpadaExamples SpatialCSL.SpadaArithmetic SpatialCSL.SpadaElaboration SpatialCSL.SpadaProgramProofs SpatialCSL.SpadaKernelProofs SpatialCSL.SpadaRoutingExamples SpatialCSL.SummaLocalProof
numeric-test: SpadaArithmetic.vo
	mkdir -p _build
	$(ROCQ) compile $(FLAGS) SpadaNumericExtract.v
	$(OCAMLC) -c -o _build/spada_numeric.cmi _build/spada_numeric.mli
	$(OCAMLC) -I _build -c -o _build/spada_numeric.cmo _build/spada_numeric.ml
	$(OCAMLC) -I _build -c -o _build/numeric_driver.cmo numeric_driver.ml
	$(OCAMLC) -I _build -o _build/numeric_driver _build/spada_numeric.cmo _build/numeric_driver.cmo
	$(PYTHON) -m unittest -v test_spada_arithmetic

SpadaRefinement.vo: SpadaRefinement.v SpadaEquivalence.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaKernelProofs.vo: SpadaKernelProofs.v SpadaRefinement.vo SpadaElaboration.vo SpadaExamples.vo SpadaArithmetic.vo
	$(ROCQ) compile $(FLAGS) $<

SpadaRouting.vo: SpadaRouting.v SpadaElaboration.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaRoutingCSL.vo: SpadaRoutingCSL.v SpadaRouting.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaDeployment.vo: SpadaDeployment.v SpadaRouting.vo SpadaKernelProofs.vo
	$(ROCQ) compile $(FLAGS) $<
SpadaRoutingExamples.vo: SpadaRoutingExamples.v SpadaDeployment.vo SpadaRoutingCSL.vo SpadaExamples.vo SpadaArithmetic.vo
	$(ROCQ) compile $(FLAGS) $<

Summa.vo: Summa.v SpadaArithmetic.vo SpadaElaboration.vo
	$(ROCQ) compile $(FLAGS) $<
summa-emit: Summa.vo SummaExtract.v summa_emit.ml
	mkdir -p _build
	$(ROCQ) compile $(FLAGS) SummaExtract.v
	$(OCAMLC) -c -o _build/summa_generated.cmi _build/summa_generated.mli
	$(OCAMLC) -I _build -c -o _build/summa_generated.cmo _build/summa_generated.ml
	$(OCAMLC) -I _build -c -o _build/summa_emit.cmo summa_emit.ml
	$(OCAMLC) -I _build -o _build/summa_emit _build/summa_generated.cmo _build/summa_emit.cmo
	./_build/summa_emit
summa: summa-emit
	$(PYTHON) spada_bridge.py generated-spada/summa-baseline.json --output generated-spada/summa-baseline
	$(PYTHON) spada_bridge.py generated-spada/summa-cached.json --output generated-spada/summa-cached
SummaLocalProof.vo: SummaLocalProof.v Summa.vo
	$(ROCQ) compile $(FLAGS) $<
summa-test: summa-emit SummaLocalProof.vo
	$(ROCQ) check -silent $(FLAGS) SpatialCSL.Summa SpatialCSL.SummaLocalProof
	$(PYTHON) -m unittest -v test_summa

# Development-host step only; the simulator runner never calls this target.
summa-perf-sources: summa-emit
	$(PYTHON) spada_bridge.py generated-spada/summa-baseline.json --arch wse3 --benchmarking --output generated-spada/summa-perf-baseline-wse3
	$(PYTHON) spada_bridge.py generated-spada/summa-cached.json --arch wse3 --benchmarking --output generated-spada/summa-perf-cached-wse3

ChainReduce.vo: ChainReduce.v SpadaIR.vo
	$(ROCQ) compile $(FLAGS) $<
ChainReduceVariant.vo: ChainReduceVariant.v ChainReduce.vo
	$(ROCQ) compile $(FLAGS) $<
chain-emit: ChainReduceVariant.vo ChainReduceExtract.v chain_emit.ml
	mkdir -p _build
	$(ROCQ) compile $(FLAGS) ChainReduceExtract.v
	$(OCAMLC) -c -o _build/chain_generated.cmi _build/chain_generated.mli
	$(OCAMLC) -I _build -c -o _build/chain_generated.cmo _build/chain_generated.ml
	$(OCAMLC) -I _build -c -o _build/chain_emit.cmo chain_emit.ml
	$(OCAMLC) -I _build -o _build/chain_emit _build/chain_generated.cmo _build/chain_emit.cmo
	./_build/chain_emit generated-spada
chain: chain-emit
	$(PYTHON) spada_bridge.py generated-spada/chain-reduce.json --arch wse3 --output generated-spada/chain-reduce-wse3
	$(PYTHON) spada_bridge.py generated-spada/chain-reduce-recvfirst.json --arch wse3 --output generated-spada/chain-reduce-recvfirst-wse3
