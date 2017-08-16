-------------------------------------------------------------------------
		--	Assinaturas
-------------------------------------------------------------------------

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

one sig CentralAtendimento{
	motoboysCentral: set Motoboy,
	listaDeEspera: set Cliente
}

-------------------------------------------------------------------------
		--	Funções
-------------------------------------------------------------------------

fun getMotoboysCentral[c:CentralAtendimento] : set Motoboy{
	c.motoboysCentral
}

fun getMotoboysRegiao[r:Regiao]: set Motoboy{
	r.pizzaria.motoboys
}

fun regiaoCliente[c:Cliente] : one Regiao{
	c.regiao
}

fun adicionaCentral[m: Motoboy, c:CentralAtendimento] : set Motoboy{
	m + c.motoboysCentral
}

fun adicionaListaDeEspera[c:Cliente, ce:CentralAtendimento]: set Cliente{
	c+ ce.listaDeEspera
}

-------------------------------------------------------------------------
		--	Predicados
-------------------------------------------------------------------------

pred temDisponivel[c:CentralAtendimento]{
	no c.motoboysCentral
}

pred estaDisponivel[m:Motoboy, c:CentralAtendimento]{
	!(m in c.motoboysCentral)
}

pred saoMesmaRegiao[m:Motoboy, c:Cliente]{
	m.regiao = c.regiao
}

pred estahEmDelivery[m:Motoboy, c:CentralAtendimento]{
	m in c.motoboysCentral
}

pred pedido[c:Cliente, ce:CentralAtendimento]{
	some m:getMotoboysRegiao[c.regiao] |(
	estaDisponivel[m, ce] =>  m in adicionaCentral[m , ce]
	else c in adicionaListaDeEspera[c, ce])
}

pred pedidPorMotoboyo[c:Cliente, m:Motoboy, ce:CentralAtendimento]{
	(saoMesmaRegiao[m, c] and estaDisponivel[m, ce]) => m in adicionaCentral[m , ce] 
	else c in adicionaListaDeEspera[c, ce]
}


-------------------------------------------------------------------------
		--	Fatos
-------------------------------------------------------------------------

fact {
	all p:Pizzaria | one p.~pizzaria -- Toda região com exatamente uma pizzaria, sem repetições.
	all m:Motoboy | one m.~motoboys -- Cada grupo de motoboys(3) relacionados apenas a uma pizzaria. 
	all n:NumCadastro | one n.~numCadastro -- Cada motoboy com seu próprio num de cadastro.
	all r:Regiao | r.pizzaria.motoboys.regiao = r -- Motoboys com a mesma região de sua pizzaria.
}

-------------------------------------------------------------------------
		--	Asserts
-------------------------------------------------------------------------

assert regioesComDiferentesPizzarias{
	no r1, r2: Regiao, p:Pizzaria | r1 != r2 && p in r1.pizzaria && p in r2.pizzaria 
}

assert semMotoboysIguais{
	no p1, p2:Pizzaria, m:Motoboy | p1 != p2 && m in p1.motoboys && m in p2.motoboys
}

assert semMesmoNumCadastro{
	no m1, m2:Motoboy | m1 != m2 && m1.numCadastro = m2.numCadastro
}

-------------------------------------------------------------------------
		--	Checks
-------------------------------------------------------------------------
	
check  regioesComDiferentesPizzarias for 15
check semMotoboysIguais for 15
check semMesmoNumCadastro for 15




//run { some c:Cliente, ce:CentralAtendimento |  pedido [c, ce]} for 15

pred show[]{}

run show for 15 -- Obs: Ativar o Magic Layout para uma melhor visualização das relações.
