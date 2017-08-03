one sig Pizzaria{
	motoboys: set Motoboy
}

sig Motoboy{}

abstract sig Regiao{}

one sig Norte extends Regiao{}

one sig Sul extends Regiao{}

one sig Leste extends Regiao{}

one sig Oeste extends Regiao{}

one sig Centro extends Regiao{}

fact{
	all p:Pizzaria | #(p.motoboys) = 3
}


pred show[]{}

run show
