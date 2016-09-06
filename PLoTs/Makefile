# Makefile for GFJ

all : uFJ.vo FJ.vo iFJ.vo uiFJ.vo GFJ.vo FGJ.vo GiFJ.vo FiGJ.vo

FJ_tactics.vo : FJ_tactics.v
	$(TIME) coqc FJ_tactics.v

cFJ.vo : cFJ.v FJ_tactics.vo
	$(TIME) coqc cFJ.v

Interface.vo : Interface.v
	$(TIME) coqc Interface.v

Cast.vo : Cast.v
	$(TIME) coqc Cast.v

Generic.vo : Generic.v
	$(TIME) coqc Generic.v

Generic_Interface.vo : Generic_Interface.v FJ_tactics.vo Generic.vo cFJ.vo Interface.vo 
	$(TIME) coqc Generic_Interface.v

Generic_Cast.vo : Generic_Cast.v FJ_tactics.vo Generic.vo cFJ.vo Cast.vo 
	$(TIME) coqc Generic_Cast.v

uFJ.vo : uFJ.v cFJ.vo FJ_Tactics.vo
	$(TIME) coqc uFJ.v

FJ.vo : FJ.v Cast.vo cFJ.vo FJ_Tactics.vo
	$(TIME) coqc FJ.v

iFJ.vo : iFJ.v Interface.vo cFJ.vo FJ_Tactics.vo 
	$(TIME) coqc iFJ.v

uiFJ.vo : uiFJ.v FJ_Tactics.vo cFJ.vo Cast.vo Interface.vo 
	$(TIME) coqc uIFJ.v

GFJ.vo : GFJ.v FJ_Tactics.vo cFJ.vo Generic.vo
	$(TIME) coqc GFJ.v

GiFJ.vo : GiFJ.v FJ_Tactics.vo cFJ.vo Generic.vo Interface.vo Generic_Interface.vo
	$(TIME) coqc GiFJ.v

FGJ.vo : FGJ.v FJ_Tactics.vo cFJ.vo Generic.vo Cast.vo Generic_Cast.vo
	$(TIME) coqc FGJ.v

FiGJ.vo : FiGJ.v FJ_Tactics.vo cFJ.vo Generic.vo Interface.vo Cast.vo Generic_Cast.vo Generic_Interface.vo
	$(TIME) coqc FiGJ.v

clean : 
	rm *.vo *.glob



