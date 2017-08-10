some sig Pizzaria{
	motoboys: set Motoboy
}

sig NumCadastro{}

sig Cliente{
	regiao: one Regiao
}

sig Motoboy{
	regiao: one Regiao,
	numCadastro: one NumCadastro
}

abstract sig Regiao{}

one sig Norte extends Regiao{
	pizzaria: one Pizzaria
}

one sig Sul extends Regiao{
	pizzaria: one Pizzaria
}

one sig Leste extends Regiao{
	pizzaria: one Pizzaria
}

one sig Oeste extends Regiao{
	pizzaria: one Pizzaria
}

one sig Centro extends Regiao{
	pizzaria: one Pizzaria
}

fact{
	all p:Pizzaria | #(p.motoboys) = 3
	#Pizzaria = 5
}

fact{
	#Cliente = 5
}

pred show[]{}

run show for 5
