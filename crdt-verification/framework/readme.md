# User Guide

Para compilar e executar esta framework, será preciso ter instalado o opam, juntamente com o Dune.

Para instalar o opam pode correr os seguintes comandos:

```bash
sudo apt update
sudo apt install opam
opam init
eval $(opam env)
```

(macOS)

```bash
brew install opam
opam init
eval $(opam env)
```

Apóes o opam estar instalado, para instalar o dune pode correr o seguinte comando:

```bash
opam install dune
```

Para compilar o projeto basta correr o seguinte comando:

```bash
dune build
```

Para processar o ficheiro input basta correr o seguinte comando após ter feito dune build:

```bash
dune exec framework -- file.crdt
```
