# User Guide

Esta diretoria contém os ficheiros gerados para why3 pela framework.

Para instalar o why3 e alguns solvers:

```bash
opam install why3 why3-ide alt-ergo
sudo apt install z3
```

(macOS)

```bash
brew install z3
```

O seguinte comando faz com que o why3 detete estes novos solvers:

```bash
why3 config detect
```

Para executar o why3 e verificar o ficheiro gerado, corra os seguintes comandos:

```bash
eval $(opam env)
why3 ide file.mlw
```
