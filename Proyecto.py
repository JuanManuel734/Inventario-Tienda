#!/usr/bin/env python3
"""Inventario de tienda con programación funcional (Unidad 2) en Python.

Sin tkinter y sin instalar nada: la interfaz es una página web local que se
abre sola en el navegador (servidor con la biblioteca estándar).
Ejecutar:  python Proyecto.py     (Ctrl+C para cerrar)

Arquitectura: NÚCLEO PURO (funciones sin efectos) + BORDE IMPURO (Almacen Firebird,
servidor web). Los comentarios [..] indican el concepto aplicado.
"""
import json
import operator
import webbrowser
from datetime import datetime
from functools import partial, reduce
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from itertools import islice
from pathlib import Path
from threading import Lock
from typing import NamedTuple
from urllib.parse import parse_qs, urlparse

from firebird.driver import connect


# ═══════════ 2.1 TIPOS DE DATOS E INMUTABILIDAD ═══════════
# [Inmutabilidad] NamedTuple = tupla con nombres: nunca se modifica, se crea otra (_replace)
class Producto(NamedTuple):
    sku: str
    nombre: str
    categoria: str
    precio: float
    stock: int
    minimo: int


class Movimiento(NamedTuple):
    id: int
    fecha: str
    sku: str
    tipo: str
    cantidad: int
    nota: str


class Estado(NamedTuple):          # todo el inventario es UN valor inmutable
    productos: tuple
    movimientos: tuple


class Resultado(NamedTuple):       # en vez de excepciones: ok + nuevo estado + mensaje
    ok: bool
    estado: Estado
    mensaje: str


# ═══════════ 2.7 EVALUACIÓN PEREZOSA: generadores ═══════════
def generar_skus():                # [Generador infinito] produce P-001, P-002... bajo demanda
    n = 1
    while True:
        yield f"P-{n:03d}"
        n += 1


def sku_libre(estado):
    usados = {p.sku for p in estado.productos}                 # comprensión de conjunto
    return next(s for s in generar_skus() if s not in usados)  # toma solo el primero libre



# ═══════════ 2.2 FUNCIONES: primera clase, orden superior, lambda ═══════════
def num(x, defecto=0.0):
    try:
        return float(x)
    except (TypeError, ValueError):
        return defecto


def comparar(op, campo, valor):    # [Orden superior + operator] fabrica un predicado
    return lambda p: op(getattr(p, campo), valor)


def todos(*preds):                 # [Predicados] combinar con "and"
    return lambda x: all(f(x) for f in preds)


def negar(pred):                   # [Predicados] "not"
    return lambda x: not pred(x)


def componer(*fs):                 # [Orden superior] f3(f2(f1(x))) con reduce
    return lambda x: reduce(lambda acc, f: f(acc), fs, x)


def pipeline(datos, *fs):
    return componer(*fs)(datos)


valor_stock = lambda p: p.precio * p.stock                     # [lambda] función pura
es_agotado = comparar(operator.eq, "stock", 0)                 # [operator] eq como función
es_bajo = lambda p: 0 < p.stock <= p.minimo
es_ok = lambda p: p.stock > p.minimo

# [Funciones como valores] diccionarios de funciones (estrategias intercambiables)
ESTADOS = {"agotado": es_agotado, "bajo": es_bajo, "ok": es_ok}
ORDENES = {"nombre": lambda p: p.nombre.lower(), "sku": operator.attrgetter("sku"),
           "precio": operator.attrgetter("precio"), "stock": operator.attrgetter("stock"),
           "valor": valor_stock}


# ═══════════ 2.5 LISTAS: map / filter / reduce / comprensiones / pipeline ═══════════
def construir_filtros(f):
    texto = f.get("texto", "").strip().lower()
    cat, est = f.get("categoria", ""), f.get("estado", "")
    activos = [
        (texto, lambda p: texto in p.nombre.lower() or texto in p.sku.lower()),
        (cat, comparar(operator.eq, "categoria", cat)),
        (est, ESTADOS.get(est)),
        (f.get("pmin"), comparar(operator.ge, "precio", num(f.get("pmin")))),
        (f.get("pmax"), comparar(operator.le, "precio", num(f.get("pmax")))),
    ]
    return todos(*[pred for activo, pred in activos if activo])


def listar(estado, f):             # datos → filter → sorted → tuple
    orden = ORDENES.get(f.get("orden"), ORDENES["nombre"])
    return pipeline(estado.productos,
                    partial(filter, construir_filtros(f)),
                    partial(sorted, key=orden, reverse=f.get("desc") == "1"),
                    tuple)


def resumen(ps):
    suma = lambda fn: reduce(lambda acc, p: acc + fn(p), ps, 0)          # [reduce]
    return {"productos": len(ps), "unidades": suma(lambda p: p.stock),
            "valor": round(suma(valor_stock), 2),
            "bajo": len(list(filter(es_bajo, ps))), "agotados": len(list(filter(es_agotado, ps)))}


def valor_por_categoria(ps):       # [reduce] construye un dict NUEVO en cada paso (sin mutar)
    return reduce(lambda acc, p: {**acc, p.categoria: round(acc.get(p.categoria, 0) + valor_stock(p), 2)}, ps, {})


def histograma(ps, paso=20, tope=140):   # [range] intervalos de stock: 0-19, 20-39, ...
    filas = [{"rango": f"{a}-{a + paso - 1}", "cantidad": len([p for p in ps if a <= p.stock < a + paso])}
             for a in range(0, tope, paso)]
    return filas + [{"rango": f"{tope}+", "cantidad": len([p for p in ps if p.stock >= tope])}]


def por_reabastecer(ps):
    return list(map(lambda p: {**p._asdict(), "sugerido": p.minimo * 2 - p.stock},
                    filter(negar(es_ok), ps)))


def fila_producto(p):
    return {**p._asdict(), "valor": round(valor_stock(p), 2),
            "estado": next(n for n, fn in ESTADOS.items() if fn(p))}


def recientes(estado, tipo="", limite=40):   # [Perezoso] reversed/filter/islice no crean listas intermedias
    pred = (lambda m: m.tipo == tipo) if tipo else (lambda m: True)
    return list(islice(filter(pred, reversed(estado.movimientos)), limite))


# ═══════════ 2.6 RECURSIVIDAD Y ÁRBOLES: nodo = (producto, izquierda, derecha) ═══════════
def construir_arbol(ps):           # árbol binario de búsqueda equilibrado por SKU (recursivo)
    if not ps:                     # caso base
        return None
    m = len(ps) // 2
    return (ps[m], construir_arbol(ps[:m]), construir_arbol(ps[m + 1:]))


def altura(a):
    return 0 if a is None else 1 + max(altura(a[1]), altura(a[2]))


def valor_arbol(a):                # igual que suma_arbol() de la presentación
    return 0 if a is None else valor_stock(a[0]) + valor_arbol(a[1]) + valor_arbol(a[2])


def buscar(a, sku, camino=()):     # devuelve (producto | None, nodos visitados)
    if a is None:
        return None, camino
    p, izq, der = a
    camino = camino + (p.sku,)
    if sku == p.sku:
        return p, camino
    return buscar(izq if sku < p.sku else der, sku, camino)


def inorden(a):                    # [Generador recursivo] recorrido ordenado
    if a is not None:
        yield from inorden(a[1])
        yield a[0]
        yield from inorden(a[2])


def arbol_a_dict(a):
    return None if a is None else {"sku": a[0].sku, "nombre": a[0].nombre,
                                   "izq": arbol_a_dict(a[1]), "der": arbol_a_dict(a[2])}


# ═══════════ ACCIONES PURAS: (estado, datos) → Resultado con estado NUEVO ═══════════
REGLAS = [(lambda d: d["nombre"] != "", "El nombre es obligatorio."),
          (lambda d: d["categoria"] != "", "La categoría es obligatoria."),
          (lambda d: d["precio"] > 0, "El precio debe ser mayor a 0."),
          (lambda d: d["stock"] >= 0, "El stock no puede ser negativo."),
          (lambda d: d["minimo"] >= 0, "El stock mínimo no puede ser negativo.")]


def limpiar(d):
    return {"nombre": str(d.get("nombre", "")).strip(), "categoria": str(d.get("categoria", "")).strip(),
            "precio": num(d.get("precio")), "stock": int(num(d.get("stock"))), "minimo": int(num(d.get("minimo")))}


def errores(d):
    return [msg for regla, msg in REGLAS if not regla(d)]


def agregar(estado, d):
    d = limpiar(d)
    if errores(d):
        return Resultado(False, estado, " ".join(errores(d)))
    nuevo = Producto(sku_libre(estado), **d)
    return Resultado(True, estado._replace(productos=estado.productos + (nuevo,)), f"Producto {nuevo.sku} agregado.")


def editar(estado, sku, d):
    d = limpiar(d)
    if errores(d):
        return Resultado(False, estado, " ".join(errores(d)))
    if sku not in {p.sku for p in estado.productos}:
        return Resultado(False, estado, "El producto no existe.")
    ps = tuple(Producto(sku, **d) if p.sku == sku else p for p in estado.productos)
    return Resultado(True, estado._replace(productos=ps), f"{sku} actualizado.")


def eliminar(estado, sku):
    ps = tuple(filter(lambda p: p.sku != sku, estado.productos))
    return Resultado(True, estado._replace(productos=ps), f"{sku} eliminado.")


def mover(estado, sku, tipo, cantidad, nota, fecha):   # la fecha llega como argumento: la función sigue pura
    prod = next((x for x in estado.productos if x.sku == sku), None)
    delta = {"entrada": cantidad, "salida": -cantidad}.get(tipo)
    if prod is None or delta is None or cantidad <= 0:
        return Resultado(False, estado, "Movimiento inválido.")
    if prod.stock + delta < 0:
        return Resultado(False, estado, f"Stock insuficiente: solo hay {prod.stock}.")
    mov = Movimiento(len(estado.movimientos) + 1, fecha, sku, tipo, cantidad, nota)
    ps = tuple(x._replace(stock=x.stock + delta) if x.sku == sku else x for x in estado.productos)
    return Resultado(True, Estado(ps, estado.movimientos + (mov,)), f"{tipo.capitalize()} de {cantidad} en {sku}.")

# ═══════════ BORDE IMPURO: Firebird ═══════════
# La lógica funcional de arriba no conoce Firebird.
# La base de datos se busca automáticamente junto a este archivo:
#     inventario.fdb
class Almacen:
    def __init__(self):
        self.lock = Lock()
        self.pasado, self.futuro = [], []
        self.estado = self._cargar()

    def _conexion(self):
        # La ruta queda junto a Proyecto.py.
        ruta_bd = str(Path(__file__).with_name("inventario.fdb").resolve())
        return connect(
            database=ruta_bd,
            user="SYSDBA",
            password="masterkey"
        )

    def _cargar(self):
        cn = None
        cur = None
        try:
            cn = self._conexion()
            cur = cn.cursor()

            cur.execute("""
                SELECT sku, nombre, categoria, precio, stock, minimo
                FROM productos
                ORDER BY sku
            """)
            productos = tuple(
                Producto(
                    p[0], p[1], p[2],
                    float(p[3]), int(p[4]), int(p[5])
                )
                for p in cur.fetchall()
            )

            cur.execute("""
                SELECT id, fecha, sku, tipo, cantidad, nota
                FROM movimientos
                ORDER BY id
            """)
            movimientos = tuple(
                Movimiento(
                    int(m[0]),
                    m[1].strftime("%Y-%m-%d %H:%M") if hasattr(m[1], "strftime") else str(m[1]),
                    m[2], m[3], int(m[4]), m[5] or ""
                )
                for m in cur.fetchall()
            )

            return Estado(productos, movimientos)

        except Exception as e:
            print(f"Error conectando a Firebird: {e}")
            print("Comprueba que exista inventario.fdb junto a Proyecto.py y que Firebird esté instalado.")
            return Estado((), ())
        finally:
            if cur is not None:
                cur.close()
            if cn is not None:
                cn.close()

    def _guardar_estado(self, anterior, nuevo):
        """Guarda el estado nuevo en Firebird dentro de una transacción."""
        cn = self._conexion()
        cur = cn.cursor()
        try:
            # Primero movimientos y después productos.
            cur.execute("DELETE FROM movimientos")
            cur.execute("DELETE FROM productos")

            if nuevo.productos:
                cur.executemany("""
                    INSERT INTO productos
                        (sku, nombre, categoria, precio, stock, minimo)
                    VALUES (?, ?, ?, ?, ?, ?)
                """, [
                    (p.sku, p.nombre, p.categoria, p.precio, p.stock, p.minimo)
                    for p in nuevo.productos
                ])

            if nuevo.movimientos:
                cur.executemany("""
                    INSERT INTO movimientos
                        (id, fecha, sku, tipo, cantidad, nota)
                    VALUES (?, ?, ?, ?, ?, ?)
                """, [
                    (
                        m.id,
                        datetime.strptime(m.fecha, "%Y-%m-%d %H:%M"),
                        m.sku,
                        m.tipo,
                        m.cantidad,
                        m.nota
                    )
                    for m in nuevo.movimientos
                ])

            cn.commit()

        except Exception:
            cn.rollback()
            raise
        finally:
            cur.close()
            cn.close()

    def aplicar(self, fn, *args):
        with self.lock:
            r = fn(self.estado, *args)
            if r.ok:
                anterior = self.estado
                self._guardar_estado(anterior, r.estado)
                self.pasado.append(anterior)
                self.futuro.clear()
                self.estado = r.estado
            return r

    def viaje(self, origen, destino, verbo):
        with self.lock:
            if not origen:
                return Resultado(False, self.estado, f"No hay nada que {verbo}.")

            anterior = self.estado
            nuevo = origen[-1]

            self._guardar_estado(anterior, nuevo)

            destino.append(self.estado)
            self.estado = origen.pop()

            return Resultado(True, self.estado, f"{verbo.capitalize()} realizado.")


ALM = Almacen()

def payload(alm, f):
    e = alm.estado
    ps = e.productos
    arbol = construir_arbol(sorted(ps, key=operator.attrgetter("sku")))
    sku = f.get("buscar", "").strip().upper()
    hallado, camino = buscar(arbol, sku) if sku else (None, ())
    return {"productos": list(map(fila_producto, listar(e, f))), "resumen": resumen(ps),
            "categorias": sorted({p.categoria for p in ps}), "porCategoria": valor_por_categoria(ps),
            "histograma": histograma(ps), "reabastecer": por_reabastecer(ps),
            "movimientos": [m._asdict() for m in recientes(e, f.get("tipo", ""))],
            "arbol": arbol_a_dict(arbol), "altura": altura(arbol), "valorArbol": round(valor_arbol(arbol), 2),
            "inorden": [p.sku for p in inorden(arbol)], "camino": list(camino), "encontrado": hallado is not None,
            "puedeDeshacer": bool(alm.pasado), "puedeRehacer": bool(alm.futuro)}


class Handler(BaseHTTPRequestHandler):
    def _enviar(self, codigo, cuerpo, tipo="application/json; charset=utf-8"):
        datos = cuerpo.encode("utf-8")
        self.send_response(codigo)
        self.send_header("Content-Type", tipo)
        self.send_header("Content-Length", str(len(datos)))
        self.end_headers()
        self.wfile.write(datos)

    def do_GET(self):
        u = urlparse(self.path)
        if u.path == "/":
            return self._enviar(200, HTML, "text/html; charset=utf-8")
        if u.path == "/api/datos":
            f = {k: v[0] for k, v in parse_qs(u.query).items()}     # comprensión de diccionario
            return self._enviar(200, json.dumps(payload(ALM, f), ensure_ascii=False))
        self._enviar(404, "{}")

    def do_POST(self):
        d = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")
        acciones = {               # [Funciones como valores] despacho sin cadenas de if/elif
            "agregar": lambda: ALM.aplicar(agregar, d),
            "editar": lambda: ALM.aplicar(editar, d["sku"], d),
            "eliminar": lambda: ALM.aplicar(eliminar, d["sku"]),
            "mover": lambda: ALM.aplicar(mover, d["sku"], d["tipo"], int(num(d["cantidad"])), d.get("nota", ""),
                                         datetime.now().strftime("%Y-%m-%d %H:%M")),
            "deshacer": lambda: ALM.viaje(ALM.pasado, ALM.futuro, "deshacer"),
            "rehacer": lambda: ALM.viaje(ALM.futuro, ALM.pasado, "rehacer"),
            "reiniciar": lambda: (setattr(ALM, "estado", ALM._cargar()) or Resultado(True, ALM.estado, "Datos recargados desde Firebird.")),
        }
        accion = self.path.rsplit("/", 1)[-1]
        r = acciones[accion]() if accion in acciones else Resultado(False, ALM.estado, "Acción desconocida.")
        self._enviar(200, json.dumps({"ok": r.ok, "mensaje": r.mensaje}, ensure_ascii=False))

    def log_message(self, *args):
        pass


# La interfaz HTML/CSS/JavaScript vive junto a este archivo y se sirve en GET /.
HTML = Path(__file__).with_name("index.html").read_text(encoding="utf-8")


def main():
    for puerto in range(8765, 8785):
        try:
            srv = ThreadingHTTPServer(("127.0.0.1", puerto), Handler)
            break
        except OSError:
            continue
    else:
        raise SystemExit("No hay puertos libres entre 8765 y 8784.")
    url = f"http://127.0.0.1:{puerto}"
    print(f"Inventario funcional en {url}  (Ctrl+C para cerrar)")
    print("Base de datos: Firebird / inventario.fdb")
    webbrowser.open(url)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nCerrado.")


if __name__ == "__main__":
    main()