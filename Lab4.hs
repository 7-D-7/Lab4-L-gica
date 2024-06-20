
module Lab4Solution where
------------------- Estudiante/s -------------------
-- Nombres y apellidos: 
-- Números: 
----------------------------------------------------

import Prelude
import Data.List

import Lab3

type Nat = Int

----------------------------------------------------------------------------------
-- 1. Veraces y mentirosos
----------------------------------------------------------------------------------

-- Variables proposicionales:
--Habitante A
a :: L
a = V "A es caballero"

--Habitante B
b :: L
b = V "B es caballero"

--Habitante C
c :: L
c = V "C es caballero"

--PRE: recibe una lista de interpretaciones
--POS: retorna True si la lista solo tiene una interpretacion
listaUnica :: [[a]] -> Bool
listaUnica xs = length xs == 1

--PRE: recibe una lista de interpretaciones
--POS: Procesa las interpretaciones, devolviendo "es caballero" si es True, o "es escudero" si es False
procesarModeloDado :: [I] -> [String]
procesarModeloDado l = map procesar (nubBy (\x y -> fst x == fst y) (concat l))
  where
    procesar (x, True)  = x
    procesar (x, False) = (head x : []) ++ " es escudero"

--PRE: recibe una formula de logica proposicional
--POS: retorna los roles de cada participante si existe una sola interpretacion, o retorna una lista vacia si existe mas de una interpretacion o no existen interpretaciones
determinarRoles :: L -> [String]
determinarRoles f
  |listaUnica (modelos f) = procesarModeloDado (modelos f)
  |otherwise = "No se puede determinar quien es quien" : []

-- Respuesta: ["B es caballero","A es escudero"] (determinarRoles ej1)
ej1 :: L
ej1 = Bin (Bin a Iff (Bin (Neg a) And (Neg b))) And (Bin b Iff (Bin a Or b)) -- ((a <-> (¬a /\ ¬b)) /\ (b <-> (a \/ b)))

-- Respuesta: ["A es escudero","B es caballero"] (determinarRoles ej2)
ej2 :: L
ej2 = Bin (Bin a Iff (Bin (Neg a) And (Neg b))) And (Bin b Iff (Bin (Neg a) Or (Neg b))) -- ((a <-> (¬a /\ ¬b)) /\ (b <-> (¬a \/ ¬b)))

-- Respuesta: ["No se puede determinar quien es quien"] (determinarRoles ej3)
ej3 :: L
ej3 = Bin (Bin b Iff (Neg a)) And (Bin c Iff (Neg b)) -- ((b <-> ¬a) /\ (c <-> ¬b))


----------------------------------------------------------------------------------
-- 2. Planificación de vigilancia
----------------------------------------------------------------------------------
-- 2.1) Respuesta: 
--Sí, es posible realizar una planificación básica si 𝑟 > 𝑧. En esta situacion, tenemos más robots que zonas, lo cual significa que siempre habrá 
--robots disponibles para cada zona sin necesidad de que ningún robot vigile más de una zona al mismo tiempo.
--Se podría asignar un robot diferente a cada zona en cada franja temporal.

-- 2.2) Respuesta: 
--No, no es posible realizar una planificación básica si 𝑟 < 𝑧. Cuando hay menos robots que zonas, no se puede cumplir la condición A (todo robot 
--en cualquier momento vigila alguna zona) y B (nunca asignamos más de un robot en la misma zona) al mismo tiempo. En cada franja 
--temporal habrá necesariamente algunas zonas sin vigilancia o algunos robots tendrán que vigilar más de una zona. 

restriccionA :: Nat -> Nat -> Nat -> L -- "Todo  robot  en  cualquier  momento  vigila  alguna  zona."
restriccionA r z t = bigAnd [1..r] (\x -> bigAnd [1..t] (\y -> bigOr [1..z] (\w -> (v3 "patrulla" x w y))))  -- (Vr)(Vt)(∃z)P(r,z,t)

restriccionB :: Nat -> Nat -> Nat -> L  -- "Nunca  asignamos  mas  de  un  robot  en  la  misma  zona."
restriccionB r z t = bigAnd [1..r] (\x -> (bigAnd [1..t] (\y -> (bigAnd [1..z] (\w -> (bigAnd ([1..r]\\[x]) (\s -> (Bin (v3 "patrulla" x w y) Imp (Neg (v3 "patrulla" s w y)))))))))) -- (Vr)(Vt)(Vz)(Vr`)(P(r,z,t) -> ¬P(r`,z,t)))

-- 2.3)
-- Pre: recibe 
--        nr - número de robots
--        nz - número de zonas de vigilancia
--        nt - número de franjas temporales
-- Pos: retorna una fórmula de LP formalizando el problema de planificacion básica.
planAB :: Nat -> Nat -> Nat -> L
planAB nr nz nt = Bin (restriccionA nr nz nt) And (restriccionB nr nz nt)                                                     

-- 2.4)
-- Graficar solución en la imagen planAB.png.

restriccionC :: Nat -> Nat -> Nat -> [(Nat, Nat)] -> [(Nat, Nat)] -> L
restriccionC nr nz nt ir iz = restC nr nz nt (ordenarInfo ir) (ordenarInfo iz)
  where
    restC _ _ _ [] [] = top
    restC _ _ _ [] _ = top
    restC _ _ _ _ [] = top
    restC r z t (robot:iro) (zona:izo) = bigAnd [1..t] (\w -> (Bin (v3 "patrulla" (fst robot) (fst zona) w) And (restC r z t iro izo)))

--Pre: recibe una lista de informacion de rendimiento o importancia
--Pos: retorna la lista ordenada de forma descendente por el segundo elemento del par
ordenarInfo :: [(Nat, Nat)] -> [(Nat, Nat)]
ordenarInfo [] = []
ordenarInfo l = sortBy (\(_,a) (_, b) -> compare b a) l

-- 2.5)
-- Pre: recibe
--        nr - número de robots
--        nz - número de zonas de vigilancia
--        nt - número de franjas temporales
--        ir - información de rendimiento para cada robot
--        iz - información de importancia para cada zona
-- Pos: retorna una fórmula de LP formalizando el problema de planificacion extendida.
planABC :: Nat -> Nat -> Nat -> [(Nat,Nat)] -> [(Nat,Nat)] -> L
planABC nr nz nt ir iz = Bin (planAB nr nz nt) And (restriccionC nr nz nt ir iz)

-- 2.6)
-- Información de rendimiento:
infoRobots :: [(Nat,Nat)]
infoRobots = [(1,200),(2,150),(3,100)]

-- Información de importancia:
infoZonas :: [(Nat,Nat)]
infoZonas = [(1,100),(2,230),(3,100)]   

-- Graficar solución en la imagen planABC.png.


----------------------------------------------------------------------------------
-- 3. Clique de grafo
----------------------------------------------------------------------------------

type G = (Nat, [(Nat,Nat)])


-- 3.1)
-- Pre: recibe un grafo no dirigido g y un tamaño de clique k
-- Pos: retorna una fórmula de LP formalizando el problema del k-clique 
kClique :: G -> Nat -> L
kClique g@(n,e) k = Bin tamanoK And completo
  where
    tamanoK = tamano k [1..n] []
    completo = bigAnd [1..n] (\i -> (bigAnd (indices i g) (\j -> (Neg (Bin (v "pertenece" i) And (v "pertenece" j))))))

-- Pre: recibe un tamaño de clique k y un grafo no dirigido g 
-- Pos: retorna una lista sin el elemento i y sin los x que formen un par con i
indices :: Nat -> G -> [Nat]
indices i g@(n,e) = [x | x <- [1..n] \\ [i], not ((x, i) `elem` e || (i, x) `elem` e)]

-- Pre: recibe un tamaño k, una lista y una lista que funciona como acumulador de vértices
-- Pos: Retorna una expresion relacionada con el tamano dado
tamano :: Nat -> [Nat] -> [Nat] -> L
tamano 1 is acc = bigOr [1..length is] (\i -> (Bin (v "pertenece" i) And (bigAnd [1..length (isp i)] (\j -> (Neg (v "pertenece" j))))))
    where
        isp i = is \\ (i:acc) -- is - {i} - {acc}
tamano k is acc = bigOr [1..length is] (\i -> (Bin (v "pertenece" i) And (tamano (k-1) (is \\ [i]) (i:acc))))

g5 :: G
g5 = (5, [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5),(4,5),(2,1),(3,1),(4,1),(3,2),(4,2),(4,3),(5,3),(5,4)])

-- 3.2)
g8 :: G
g8 = (8,[(1,5),(1,4),(1,6),(1,3),(2,3),(2,4),(2,7),(2,5),(3,1),(3,2),(3,8),(3,7),(3,6),(4,1),(4,2),(4,5),(4,7),(4,6),(5,2),(5,1),(5,4),
        (5,6),(5,7),(6,3),(6,1),(6,4),(6,5),(6,7),(7,8),(7,5),(7,2),(7,4),(7,3),(7,6),(8,3),(8,7)])

-- ... Mencionar las soluciones encontradas aquí ...

-- 3.3)
-- ... Mencionar solución encontrada aquí ...

-- 3.4)
-- Pre: recibe un grafo no dirigido g y un tamaño de clique k
-- Pos: retorna una fórmula de LP formalizando el problema del k-clique maximal
maxkClique :: G -> Nat -> L
maxkClique g@(n,e) k = Bin (Neg (bigOr [1..n] (\i -> (Bin (Neg (v "pertenece" i)) And (bigAnd (indices i g) (\j -> (Neg (v "pertenece" j)))))))) And (kClique g k)

-- 3.5) 
-- ... Mencionar solución encontrada aquí ...


----------------------------------------------------------------------------------
-- Funciones sugeridas
----------------------------------------------------------------------------------

-- Conjuntoria (universal finito) de fórmulas indexadas
bigAnd :: [Int] -> (Int -> L) -> L
bigAnd [] _ = top
bigAnd (x:xs) f = foldl (\acc i -> Bin acc And (f i)) (f x) xs

-- Disyuntoria (existencial finito) de fórmulas indexadas
bigOr :: [Int] -> (Int -> L) -> L
bigOr [] _ = bot
bigOr (x:xs) f = foldl (\acc i -> Bin acc Or (f i)) (f x) xs

-- Variable proposicional indexada
v :: Var -> Nat -> L
v p i = V (p ++ show i)

-- Variable proposicional triplemente indexada
v3 :: Var -> Nat -> Nat -> Nat -> L
v3 p i j k = V (p ++ show i ++ "_" ++ show j ++ "_" ++ show k)


----------------------------------------------------------------------------------
-- Algunas funciones auxiliares 
----------------------------------------------------------------------------------

-- Pre: recibe un nombre de variable p y un natural n.
-- Pos: genera todas las posibles declaraciones de variables proposicionales 
--      indexadas en el rango 1..n y en el formato SMT-LIB.
--      Por ejemplo, si n=4 tenemos 4 declaraciones de variables.
-- RECOMENDACIÓN: para imprimir en consola ejecutar (si el nombre es "p" y n=4):  
--      ghci> putStrLn (genVars "p" 4)   
genVars :: String -> Nat -> String
genVars p n = foldr (\v b -> ("(declare-fun " ++ (show v) ++ " () Bool)\n") ++ b) "" vars
  where 
    vars = [V (p ++ (show i)) | i <- [1..n]]

-- Pre: recibe un nombre de variable p y dos naturales n y m.
-- Pos: genera todas las posibles permutaciones de declaraciones de variables proposicionales
--      triplemente indexadas en el rango 1..n, 1..m y 1..l en el formato SMT-LIB.
--      Por ejemplo, si n=4, m=2 y l=3 tenemos 4*2*3=24 declaraciones de variables.
-- RECOMENDACIÓN: para imprimir en consola ejecutar (si el nombre es "p", n=4, m=2 y l=3):  
--      ghci> putStrLn (genVars3 "p" 4 2 3)   
genVars3 :: String -> Nat -> Nat -> Nat -> String
genVars3 p n m l = foldr (\v b -> ("(declare-fun " ++ (show v) ++ " () Bool)\n") ++ b) "" vars
  where 
    vars = [V (p ++ (show i) ++ "_" ++ (show j) ++ "_" ++ (show k)) | i <- [1..n], j <- [1..m], k <- [1..l]]    

-- Pre: recibe el dominio de una función finita y la función representada por una lista de parejas (una tabla).
-- Pos: retorna una relación de orden, representada por una lista de parejas, sobre los elementos del 
--      dominio de la funcion basándose en el rango asignado.
--      El orden será irreflexivo, pero no necesariamente total.
orden :: [Nat] -> [(Nat,Nat)] -> [(Nat,Nat)]
orden dom fun = [(x1,x2) | x1 <- dom, x2 <- dom, (crearf fun) x1 < (crearf fun) x2] 

-- Pre: recibe una función finita representada por una lista de parejas (una tabla).
-- Pos: retorna una funcion de haskell que se corresponde con la tabla recibida.
crearf :: [(Nat, Nat)] -> (Nat -> Nat)
crearf []         v = error $ show v ++ " indefinida!"
crearf ((d,r):xs) v = case v == d of
                        True  -> r
                        False -> crearf xs v 

-- Pre: recibe una fórmula de LP.
-- Pos: pretty printing de la fórmula en formato SMT-LIB, esto es: parentizada y prefija.
toPrefix :: L -> String
toPrefix (V p)       = p
toPrefix (Neg a)     = "(not " ++ toPrefix a ++ ")"
toPrefix (Bin a And b) = "(and " ++ toPrefix a ++ " " ++ toPrefix b ++ ")"
toPrefix (Bin a Or  b) = "(or "  ++ toPrefix a ++ " " ++ toPrefix b ++ ")"
toPrefix (Bin a Imp b) = "(=> "  ++ toPrefix a ++ " " ++ toPrefix b ++ ")"
toPrefix (Bin a Iff b) = "(= "   ++ toPrefix a ++ " " ++ toPrefix b ++ ")"