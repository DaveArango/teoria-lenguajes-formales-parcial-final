#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generador de arboles de derivacion para gramaticas independientes del contexto.

Teoria de Lenguajes Formales - Segundo parcial
Autores: Jhonatan David Vivas Arango y Valery Andrea Ortiz Mesa

El programa NO es un parser: no analiza una cadena para descubrir como se
deriva. Recibe (1) las producciones de la gramatica y (2) la secuencia de
pasos de derivacion (formas sentenciales) escrita por el usuario, comprueba
que cada paso se obtenga del anterior aplicando una produccion y construye
el arbol de derivacion correspondiente.

Uso:
    python arbol_derivacion.py GRAMATICA.txt DERIVACION.txt [--png a.png] [--dot a.dot]
    python arbol_derivacion.py            (modo interactivo)

Solo usa la biblioteca estandar de Python 3.8+. La opcion --png necesita
tener instalado Graphviz (comando "dot"); el arbol en texto no lo necesita.
"""

import argparse
import shutil
import subprocess
import sys

FLECHAS_REGLA = ("::=", "→")          # separadores admitidos entre cabeza y cuerpo
SIMBOLOS_VACIO = {"ε", "epsilon", "lambda", "λ"}
PREFIJOS_PASO = ("=>", "⇒")           # se ignoran al inicio de un paso


class ErrorDerivacion(Exception):
    """Error en la gramatica o en los pasos suministrados."""


# --------------------------------------------------------------------------
# Estructuras de datos
# --------------------------------------------------------------------------
class Nodo:
    """Nodo del arbol: un simbolo y la lista ordenada de sus hijos."""

    def __init__(self, simbolo, terminal):
        self.simbolo = simbolo
        self.terminal = terminal
        self.hijos = []


class Gramatica:
    """G = (V, Sigma, R, S) cargada desde texto."""

    def __init__(self, inicial, reglas):
        self.inicial = inicial
        self.reglas = reglas                       # lista de (cabeza, cuerpo)
        self.no_terminales = []                    # V, en orden de aparicion
        for cabeza, _ in reglas:
            if cabeza not in self.no_terminales:
                self.no_terminales.append(cabeza)
        self.terminales = []                       # Sigma
        for _, cuerpo in reglas:
            for s in cuerpo:
                if s not in self.no_terminales and s not in self.terminales:
                    self.terminales.append(s)
        if inicial not in self.no_terminales:
            raise ErrorDerivacion(
                "El simbolo inicial '%s' no tiene producciones." % inicial)

    def es_no_terminal(self, simbolo):
        return simbolo in self.no_terminales

    def describir(self):
        lineas = ["Gramatica G = (V, Σ, R, S)",
                  "  V = { " + ", ".join(self.no_terminales) + " }",
                  "  Σ = { " + ", ".join(self.terminales) + " }",
                  "  S = " + self.inicial,
                  "  R ="]
        for n, (cabeza, cuerpo) in enumerate(self.reglas, 1):
            lineas.append("    (%d) %s → %s" % (n, cabeza, " ".join(cuerpo) or "ε"))
        return "\n".join(lineas)


# --------------------------------------------------------------------------
# Lectura de la entrada
# --------------------------------------------------------------------------
def _lineas_utiles(texto):
    for linea in texto.splitlines():
        linea = linea.strip()
        if linea and not linea.startswith("#"):
            yield linea


def leer_gramatica(texto):
    """Formato: 'inicial: S' (opcional) y reglas 'A ::= alfa | beta'."""
    inicial = None
    reglas = []
    for linea in _lineas_utiles(texto):
        if linea.lower().startswith("inicial:"):
            inicial = linea.split(":", 1)[1].strip()
            continue
        flecha = next((f for f in FLECHAS_REGLA if " %s " % f in " %s " % linea), None)
        if flecha is None:
            raise ErrorDerivacion("Regla sin '::=': " + linea)
        cabeza, cuerpos = linea.split(flecha, 1)
        cabeza = cabeza.strip()
        if len(cabeza.split()) != 1:
            raise ErrorDerivacion("La cabeza debe ser un unico no terminal: " + linea)
        alternativa = []
        for simbolo in cuerpos.split() + ["|"]:
            if simbolo == "|":                      # fin de una alternativa
                cuerpo = tuple(s for s in alternativa if s not in SIMBOLOS_VACIO)
                reglas.append((cabeza, cuerpo))
                alternativa = []
            else:
                alternativa.append(simbolo)
    if not reglas:
        raise ErrorDerivacion("No se suministro ninguna regla.")
    return Gramatica(inicial or reglas[0][0], reglas)


def leer_derivacion(texto):
    """Formato: 'tipo: izquierda|derecha|libre' (opcional) y un paso por linea."""
    tipo = "libre"
    pasos = []
    for linea in _lineas_utiles(texto):
        if linea.lower().startswith("tipo:"):
            tipo = linea.split(":", 1)[1].strip().lower()
            continue
        simbolos = linea.split()
        if simbolos and simbolos[0] in PREFIJOS_PASO:
            simbolos = simbolos[1:]
        pasos.append([s for s in simbolos if s not in SIMBOLOS_VACIO])
    if tipo not in ("izquierda", "derecha", "libre"):
        raise ErrorDerivacion("Tipo de derivacion desconocido: " + tipo)
    if not pasos:
        raise ErrorDerivacion("No se suministro ningun paso de derivacion.")
    return tipo, pasos


# --------------------------------------------------------------------------
# Construccion del arbol
# --------------------------------------------------------------------------
def construir_arbol(gramatica, tipo, pasos):
    """
    Recorre los pasos. 'frontera' guarda las hojas actuales del arbol, de
    izquierda a derecha; sus simbolos forman la forma sentencial vigente.
    En cada paso se localiza el no terminal sustituido y la produccion usada,
    y a esa hoja se le agregan como hijos los simbolos del cuerpo.
    Devuelve (raiz, bitacora, frontera).
    """
    if pasos[0] != [gramatica.inicial]:
        raise ErrorDerivacion(
            "El primer paso debe ser el simbolo inicial '%s'." % gramatica.inicial)
    raiz = Nodo(gramatica.inicial, False)
    frontera = [raiz]
    bitacora = []

    for numero, siguiente in enumerate(pasos[1:], 1):
        actual = [n.simbolo for n in frontera]
        posiciones = [i for i, n in enumerate(frontera) if not n.terminal]
        if not posiciones:
            raise ErrorDerivacion(
                "Paso %d: ya no quedan no terminales por sustituir." % numero)
        if tipo == "izquierda":
            posiciones = posiciones[:1]
        elif tipo == "derecha":
            posiciones = posiciones[-1:]

        hallazgo = None
        for i in posiciones:
            for n_regla, (cabeza, cuerpo) in enumerate(gramatica.reglas, 1):
                if cabeza == actual[i] and \
                        actual[:i] + list(cuerpo) + actual[i + 1:] == siguiente:
                    hallazgo = (i, n_regla, cabeza, cuerpo)
                    break
            if hallazgo:
                break
        if hallazgo is None:
            detalle = "" if tipo == "libre" else \
                " (derivacion por la %s: solo puede sustituirse '%s')" % (
                    tipo, actual[posiciones[0]])
            raise ErrorDerivacion(
                "Paso %d invalido: de\n    %s\nno se obtiene\n    %s\n"
                "aplicando una sola produccion%s."
                % (numero, " ".join(actual), " ".join(siguiente) or "ε", detalle))

        i, n_regla, cabeza, cuerpo = hallazgo
        nodo = frontera[i]
        if cuerpo:
            nodo.hijos = [Nodo(s, not gramatica.es_no_terminal(s)) for s in cuerpo]
            frontera[i:i + 1] = nodo.hijos
        else:                                       # produccion A → ε
            nodo.hijos = [Nodo("ε", True)]
            frontera[i:i + 1] = []
        bitacora.append((numero, n_regla, cabeza, cuerpo, siguiente))
    return raiz, bitacora, frontera


# --------------------------------------------------------------------------
# Visualizacion
# --------------------------------------------------------------------------
def arbol_en_texto(nodo, prefijo="", ultimo=True, es_raiz=True):
    """Arbol jerarquico textual (cada nivel de sangria es un nivel del arbol)."""
    if es_raiz:
        lineas = [nodo.simbolo]
        extension = ""
    else:
        lineas = [prefijo + ("└── " if ultimo else "├── ") + nodo.simbolo]
        extension = prefijo + ("    " if ultimo else "│   ")
    for k, hijo in enumerate(nodo.hijos):
        lineas += arbol_en_texto(hijo, extension, k == len(nodo.hijos) - 1, False)
    return lineas


def arbol_en_dot(raiz):
    """Descripcion del arbol en lenguaje DOT (Graphviz)."""
    lineas = ["digraph arbol {",
              '  graph [ordering=out, nodesep=0.25, ranksep=0.45];',
              '  node [fontname="Helvetica", fontsize=12];',
              '  edge [arrowhead=none];']
    contador = [0]

    def visitar(nodo):
        ident = "n%d" % contador[0]
        contador[0] += 1
        etiqueta = nodo.simbolo.replace("\\", "\\\\").replace('"', '\\"')
        if nodo.hijos:                              # no terminal expandido
            estilo = "shape=ellipse"
        elif nodo.terminal:
            estilo = 'shape=box, style=filled, fillcolor="#E8E8E8"'
        else:                                       # no terminal sin expandir
            estilo = "shape=ellipse, style=dashed"
        lineas.append('  %s [label="%s", %s];' % (ident, etiqueta, estilo))
        for hijo in nodo.hijos:
            lineas.append("  %s -> %s;" % (ident, visitar(hijo)))
        return ident

    visitar(raiz)
    lineas.append("}")
    return "\n".join(lineas) + "\n"


def exportar(raiz, ruta_dot, ruta_png):
    dot = arbol_en_dot(raiz)
    if ruta_dot:
        with open(ruta_dot, "w", encoding="utf-8") as f:
            f.write(dot)
        print("Archivo DOT guardado en: " + ruta_dot)
    if ruta_png:
        if shutil.which("dot") is None:
            print("AVISO: no se encontro Graphviz ('dot'); no se genero el PNG. "
                  "Instalelo o use --dot y un visor en linea.")
            return
        subprocess.run(["dot", "-Tpng", "-Gdpi=150", "-o", ruta_png],
                       input=dot.encode("utf-8"), check=True)
        print("Imagen del arbol guardada en: " + ruta_png)


# --------------------------------------------------------------------------
# Programa principal
# --------------------------------------------------------------------------
def modo_interactivo():
    print("MODO INTERACTIVO - deje una linea vacia para terminar cada bloque.\n")
    print("Reglas (ejemplo:  E ::= E + T | T). La primera cabeza es el simbolo inicial:")
    reglas = []
    while True:
        linea = input("  regla> ").strip()
        if not linea:
            break
        reglas.append(linea)
    tipo = input("Tipo de derivacion [izquierda/derecha/libre]: ").strip() or "libre"
    print("Pasos de derivacion, una forma sentencial por linea (simbolos separados por espacios):")
    pasos = []
    while True:
        linea = input("  paso> ").strip()
        if not linea:
            break
        pasos.append(linea)
    return "\n".join(reglas), "tipo: %s\n%s" % (tipo, "\n".join(pasos))


def main():
    if hasattr(sys.stdout, "reconfigure"):          # acentos y lineas en Windows
        sys.stdout.reconfigure(encoding="utf-8")
    analizador = argparse.ArgumentParser(
        description="Genera el arbol de derivacion a partir de las reglas y "
                    "los pasos de derivacion suministrados.")
    analizador.add_argument("gramatica", nargs="?", help="archivo con las reglas")
    analizador.add_argument("derivacion", nargs="?", help="archivo con los pasos")
    analizador.add_argument("--dot", help="guardar el arbol en formato DOT")
    analizador.add_argument("--png", help="guardar el arbol como imagen (requiere Graphviz)")
    args = analizador.parse_args()

    try:
        if args.gramatica and args.derivacion:
            with open(args.gramatica, encoding="utf-8") as f:
                texto_gramatica = f.read()
            with open(args.derivacion, encoding="utf-8") as f:
                texto_derivacion = f.read()
        elif args.gramatica:
            analizador.error("faltan los pasos: indique GRAMATICA y DERIVACION, "
                             "o ningun archivo para el modo interactivo.")
        else:
            texto_gramatica, texto_derivacion = modo_interactivo()

        gramatica = leer_gramatica(texto_gramatica)
        tipo, pasos = leer_derivacion(texto_derivacion)
        raiz, bitacora, frontera = construir_arbol(gramatica, tipo, pasos)
    except (ErrorDerivacion, OSError) as error:
        print("ERROR: %s" % error)
        sys.exit(1)

    print(gramatica.describir())
    print("\nDerivacion suministrada (tipo: %s)" % tipo)
    print("  %2d. %s" % (0, gramatica.inicial))
    for numero, n_regla, cabeza, cuerpo, forma in bitacora:
        print("  %2d. %s" % (numero, " ".join(forma) or "ε"))
        print("        [regla %d: %s → %s]" % (n_regla, cabeza, " ".join(cuerpo) or "ε"))

    print("\nArbol de derivacion")
    print("\n".join(arbol_en_texto(raiz)))

    hojas = " ".join(n.simbolo for n in frontera) or "ε"
    if all(n.terminal for n in frontera):
        print("\nCadena derivada (hojas de izquierda a derecha):\n  " + hojas)
    else:
        print("\nAVISO: la derivacion esta incompleta; forma sentencial alcanzada:\n  " + hojas)
    print("Pasos aplicados: %d" % len(bitacora))

    if args.dot or args.png:
        exportar(raiz, args.dot, args.png)


if __name__ == "__main__":
    main()
