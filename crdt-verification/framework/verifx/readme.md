# User Guide

Esta diretoria contém os ficheiros gerados para VeriFx pela framework.

Todas as instruções de instalação do VeriFx estão no repositório oficial da ferramenta:
<https://github.com/verifx-prover/verifx>

Sempre que a framework gerar novos ficheiros derivados dos modules do ficheiro de input, será necessário alterar o seguinte ficheiro:

src/test/scala/org/verifx/practical/ProofTests.scala

Adicionando o seguinte código substituindo "nome_do_ficheiro" pelo nome real do ficheiro gerado,
alterando também "is_a_CvRDT" por "is_a_CmRDT" caso necessário:

```scala
"nome_do_ficheiro" should "be a CRDT" in {
  val proof = ("nome_do_ficheiro", "is_a_CvRDT")
  prove(proof)
}
```

Para correr os testes, basta correr o seguinte comando:

```bash
sbt clean compile test
```
