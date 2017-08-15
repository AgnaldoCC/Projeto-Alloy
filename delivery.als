sig Pizzaria{
	motoboys: set Motoboy
}{
	#motoboys = 3
}

some sig Cliente{
	regiao: one Regiao
}

sig Motoboy{
	regiao: one Regiao,
	numCadastro: one NumCadastro
}

sig NumCadastro{}

abstract sig Regiao{
	pizzaria: one Pizzaria
}

one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}


fact {
	all p:Pizzaria | one p.~pizzaria -- Toda região com exatamente uma pizzaria, sem repetições.
	all m:Motoboy | one m.~motoboys -- Cada grupo de motoboys(3) relacionados apenas a uma pizzaria. 
	all n:NumCadastro | one n.~numCadastro -- Cada motoboy com seu próprio num de cadastro.
	all r:Regiao | r.pizzaria.motoboys.regiao = r -- Motoboys com a mesma região de sua pizzaria.
}

assert regioesComDiferentesPizzarias{
	no r1, r2: Regiao, p:Pizzaria | r1 != r2 && p in r1.pizzaria && p in r2.pizzaria 
}

assert semMotoboysIguais{
	no p1, p2:Pizzaria, m:Motoboy | p1 != p2 && m in p1.motoboys && m in p2.motoboys
}

assert semMesmoNumCadastro{
	no m1, m2:Motoboy | m1 != m2 && m1.numCadastro = m2.numCadastro
}
	
check  regioesComDiferentesPizzarias for 15
check semMotoboysIguais for 15
check semMesmoNumCadastro for 15

pred show[]{}

run show for 15 -- Obs: Ativar o Magic Layout para uma melhor visualização das relações.
