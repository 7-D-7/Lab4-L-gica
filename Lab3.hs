
module Lab3 where
------------------- Estudiante/s -------------------
-- Nombres y apellidos: Cristhian Gribauskas
-- Números: 309715
----------------------------------------------------

import Prelude
import Data.List
import Data.Maybe

----------------------------------------------------------------------------------
-- Formalización del lenguaje y otros elementos
----------------------------------------------------------------------------------
type Var = String
type Lit = (Var,Bool)
type I = [Lit]

data L = V Var | Neg L | Bin L BC L
  deriving (Eq)

data BC = And | Or | Imp | Iff 
  deriving (Show, Eq)

data Clase = Tau | Contra | Cont
  deriving (Show, Eq)

data Consecuencia = [L] :|= L deriving (Show, Eq)  --[p, p -> q] :|= q

data Tableau = Dis [L] Tableau Tableau
              | Conj [L] Tableau
              | Hoja I

   
top = Bin (V "p") Or  (Neg $ V "p") 
bot = Bin (V "p") And (Neg $ V "p") 

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe un literal
--Pos: Retorna el literal en forma de fórmula
lit2f :: (Var, Bool) -> L
lit2f (v, True) = V v
lit2f (v, False) = Neg (V v)

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una interpretacion y una lista de formulas
--Pos: Transforma los literales de la interpretacion y los une con la lista de formulas
formulas :: I -> [L] -> [L]
formulas i f = (map lit2f i) ++ f 

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una lista de formulas
--Pos: Retorna la conjuncion de las formulas
conjuntoria :: [L] -> L
conjuntoria fs = conjuntoriaAux (reverse fs)
  where
    conjuntoriaAux [x] = x
    conjuntoriaAux (x:xs) = Bin (conjuntoriaAux xs) And x

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una lista de formulas
--Pos: Retorna la disyuncion de las formulas
disyuntoria :: [L] -> L
disyuntoria fs = disyuntoriaAux (reverse fs)
  where
    disyuntoriaAux [x] = x
    disyuntoriaAux (x:xs) = Bin (disyuntoriaAux xs) Or x

-- 1)
-- Pre: recibe una lista de asignaciones de valores de verdad sobre variables
-- Pos: retorna True si y solo si la lista es consistente, o sea representa una interpretación
esConsistente :: I -> Bool
esConsistente i = not (any (\(v, b) -> (v, not b) `elem` i && (v, b) `elem` i) i)

-- 2)
-- Pre: recibe una interpretación dada como lista de asignaciones (no vacía y consistente) 
-- Pos: retorna la interpretación expresada como una conjunción de literales
int2f :: I -> L
int2f ((v, b) : xs) = foldl (\acc (v2, b2) -> Bin acc And (if b2 then V v2 else Neg (V v2))) (if b then V v else Neg (V v)) xs

{-
fextra :: L
fextra = Bin (Bin (V "p") And (Neg (V "q"))) Or (V "q")  -- ((p /\ ¬q) \/ q)

fextraDos :: L
fextraDos = Bin (Bin (V "p") And (Neg (V "p"))) And (V "q") -- ((p /\ ¬p) /\ q)

fextraTres :: L
fextraTres = Bin (Bin (Bin (V "p") Imp (V "q")) Imp (V "p")) Imp (V "p") -- (((p --> q) --> p) --> p)
-}

-- 3)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna el tableau de f
tableau :: L -> Tableau
tableau f = tabAcc [f] []
  where
    tabAcc [] i = Hoja i
    tabAcc l@(V v : fs) i = tabAcc fs ((v, True) : i) -- Literal
    tabAcc l@(Neg (V v) : fs) i = tabAcc fs ((v, False) : i) -- Literal Negado
    tabAcc l@(Bin l1 And l2 : fs) i = Conj (formulas i l) (tabAcc (l1 : l2 : fs) i) -- Conjuntiva
    tabAcc l@(Neg (Bin l1 Or l2) : fs) i = Conj (formulas i l) (tabAcc (Neg l1 : Neg l2 : fs) i) -- Disyuntiva Negada
    tabAcc l@(Neg (Bin l1 Imp l2) : fs) i = Conj (formulas i l) (tabAcc (l1 : Neg l2 : fs) i) -- Implicacion negada
    tabAcc l@(Neg (Neg f) : fs) i = Conj (formulas i l) (tabAcc (f : fs) i) -- Doble negacion
    tabAcc l@(Bin l1 Or l2 : fs) i = Dis (formulas i l) (tabAcc (l1 : fs) i) (tabAcc (l2 : fs) i) -- Disyuntiva
    tabAcc l@(Neg (Bin l1 And l2) : fs) i = Dis (formulas i l) (tabAcc (Neg l1 : fs) i) (tabAcc (Neg l2 : fs) i) -- Conjuntiva Negada
    tabAcc l@(Bin l1 Imp l2 : fs) i = Dis (formulas i l) (tabAcc (Neg l1 : fs) i) (tabAcc (l2 : fs) i) -- Implicacion
    tabAcc l@(Bin l1 Iff l2 : fs) i = Dis (formulas i l) (tabAcc (l1 : l2 : fs) i) (tabAcc (Neg l1 : Neg l2 : fs) i) -- Bicondicional
    tabAcc l@(Neg (Bin l1 Iff l2) : fs) i = Dis (formulas i l) (tabAcc (l1 : Neg l2 : fs) i) (tabAcc (Neg l1 : l2 : fs) i) -- Bicondicional Negado



-- 4)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna True si y solo si f es sat
sat :: L -> Bool
sat f = satAux (tableau f)
  where
    satAux (Hoja i) = esConsistente i
    satAux (Conj _ t) = satAux t
    satAux (Dis _ t1 t2) = satAux t1 && satAux t2

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una formula
--Pos: Retorna una lista con las interpretaciones que son modelos de la formula
pruebaModelo :: L -> [I]
pruebaModelo f = modelosAux (tableau f)
  where
    modelosAux (Hoja i) = if (all (esConsistente) [i]) then [i] else []
    modelosAux (Conj _ t) = modelosAux t
    modelosAux (Dis _ t1 t2) = modelosAux t1 ++ modelosAux t2

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una lista de elementos
--Pos: Retorna una lista sin elementos duplicados
elimDupl :: Eq a => [a] -> [a]
elimDupl [] = []
elimDupl (x:xs)
  | elem x xs = x:(elimDupl (filter (/= x) xs))
  | otherwise = x : elimDupl xs

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una formula
--Pos: Retorna una lista con las variables de la formula
listarProp :: L -> [Var]
listarProp (V a) = [a]
listarProp (Neg l1) =  elimDupl (listarProp l1)
listarProp (Bin l1 _ l2) = elimDupl (listarProp l1 ++ listarProp l2)

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una lista de elementos
--Pos: Retorna una lista ordenada de mayor a menor
bubbleSort :: Ord a => [a] -> [a]
bubbleSort [] = []
bubbleSort xs = maximum xs : bubbleSort [y | y<-xs, y /= m]
  where m = maximum xs

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe dos listas
--Pos: Retorna True si las listas son iguales
sameList :: (Ord a) => [a] -> [a] -> Bool
sameList xs ys = reverse (bubbleSort xs) == reverse (bubbleSort ys)

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una lista de interpretaciones
--Pos: Retorna una lista con las variables de las interpretaciones
inter2var :: [I] -> [Var]
inter2var i = elimDupl(map fst (concat i))

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una lista de (Var, Bool) y una formula
--Pos: Retorna una lista de (Var, Bool) completa, es decir, usando las variables ya asignadas, genera las posibles combinaciones de esas variables asignadas con los valores True y False de las variables no asignadas de la formula
combinaciones :: [(Var, Bool)] -> L -> [[(Var, Bool)]]
combinaciones variablesAsignadas formula = [variablesAsignadas ++ zip variablesNoAsignadas values | values <- allCombinations (length variablesNoAsignadas)]
  where 
    vars = listarProp formula
    variablesAsignadasConNombres = map fst variablesAsignadas
    variablesNoAsignadas = filter (`notElem` variablesAsignadasConNombres) vars
    allCombinations 0 = [[]]
    allCombinations n = [b : bs | b <- [False, True], bs <- allCombinations (n-1)]
 
-- 5)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna una lista con todos los modelos completos de f
-- Recomendación: para imprimirlos los modelos en lineas distintas:
--                ghci> mapM_ print $ modelos f
modelos :: L -> [I]
modelos f = concat [if sameList (listarProp f) (inter2var [inter]) then [inter] else completeInter inter f | inter <- pruebaModelo f]

--Auxiliar---------------------------------------------------------------------
--Pre: Recibe una interpretacion y una formula
--Pos: Retorna una lista con las interpretaciones completas de la interpretacion
completeInter :: I -> L -> [I]
completeInter inter f = [inter ++ [(var, value)] | var <- variablesFaltantes, value <- [False, True]]
  where 
    vars = listarProp f
    variablesAsignadas = map fst inter
    variablesFaltantes = filter (`notElem` variablesAsignadas) vars

-- 6)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna la clase semántica a la que pertenece f
clasificar :: L -> Clase
clasificar f
  | null (modelos (Neg(f))) = Tau
  | null (modelos f) = Contra
  | not (null (modelos f)) && not(null (modelos (Neg(f)))) = Cont

-- 7)
-- Pre: recibe una consecuencia
-- Pos: retorna la consecuencia expresada como una fórmula de LP
cons2f :: Consecuencia -> L
cons2f ([] :|= f) = f
cons2f (p :|= f) = Bin (conjuntoria p) Imp f 

{-
pruebaParaSiete :: Consecuencia
pruebaParaSiete = [Bin (V "p") Imp (V "q"), (V "p")] :|= (V "q") -- [(p --> q),p] :|= q

pruebaParaSieteDos :: Consecuencia
pruebaParaSieteDos = [Bin (V "p") Imp (V "q"), (V "q")] :|= (V "p") -- [(p --> q),q] :|= p

pruebaParaSieteTres :: Consecuencia
pruebaParaSieteTres = [Bin p Imp q, Bin (Bin (Neg (V "s")) And (Neg (V "t"))) Imp r] :|= (Bin (Bin (Bin (Neg (V "s")) And (Neg (V "t"))) Or p) Imp (Bin r Or q))

pruebaParaSieteCuatro :: Consecuencia
pruebaParaSieteCuatro = [Bin p Imp (Bin q And r), Bin r Imp (Bin (V "s") And p), Bin (Neg (V "s")) Or (Neg p)] :|= (Bin (Neg (V "s")) Or (Neg q))

pruebaParaSieteCinco :: Consecuencia
pruebaParaSieteCinco = [Bin p Imp (Bin q And r), Bin r Imp (Bin (V "s") And p), Bin (Neg (V "s")) Or (Neg p)] :|= (Neg (p))
-}

-- 8)     
-- Pre: recibe una consecuencia
-- Pos: retorna True si y solo si la consecuencia es válida
valida :: Consecuencia -> Bool
valida p
  | clasificar (cons2f p) == Tau = True
  | otherwise = False

-- 9)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna f en FND
fnd :: L -> L
fnd f = disyuntoria [ conjuntoria [ lit2f (v, b) | (v, b) <- inter] | inter <- pruebaModelo f]

-- 10)
-- Pre: recibe una fórmula f de LP
-- Pos: retorna f en FNC
fnc :: L -> L
fnc f = conjuntoria [ disyuntoria [ lit2f (v, not b) | (v, b) <- inter] | inter <- pruebaModelo f]

{-
pruebaParaNueve :: L
pruebaParaNueve = Bin (Bin p And (Bin q Imp (Neg (p)))) Or (r) -- ((p /\ (q --> ¬p)) \/ r)

pruebaParaDiez :: L
pruebaParaDiez = Neg (Bin (Bin p And (Bin q Imp (Neg p))) Or r) -- ¬((p /\ (q --> ¬p)) \/ r)
-}

----------------------------------------------------------------------------------
-- Fórmulas del Lab1 para probar
----------------------------------------------------------------------------------
p = V "p"
q = V "q"
r = V "r"
fa :: L
fa = Bin p And (Neg (Neg q))                   -- (p ∧ ¬¬q)
fb :: L
fb = Bin p And (Bin (Neg q) And (Neg r))       -- (p ∧ ¬q ∧ ¬r)
fc :: L
fc = Bin (Neg (Neg p)) Or (Neg (Bin q And p))  -- (¬¬p ∨ ¬(q ∧ p))
fd :: L
fd = Bin (Neg (Bin r Imp r)) And fc            -- ¬(r ⊃ r) ∧ (¬¬p ∨ ¬(q ∧ p))

----------------------------------------------------------------------------------
-- Algunas funciones auxiliares 
----------------------------------------------------------------------------------

vars :: L -> [Var]
vars (V p)         = [p]
vars (Neg f)       = vars f
vars (Bin f1 _ f2) = nub (vars f1 ++ vars f2)

----------------------------------------------------------------------------------
-- Pretty Printing
----------------------------------------------------------------------------------
instance Show L where
  show (V p)           = p
  show (Neg (Neg a))   = "¬" ++ show (Neg a)
  show (Neg (V p))     = "¬" ++ show (V p)
  show (Neg a)         = "¬" ++ show a ++ ""
  show (Bin a And b)   = "(" ++ show a ++ " /\\ " ++ show b ++ ")"
  show (Bin a Or b)    = "(" ++ show a ++ " \\/ " ++ show b ++ ")"
  show (Bin a Imp b)   = "(" ++ show a ++ " --> " ++ show b ++ ")"
  show (Bin a Iff b)   = "(" ++ show a ++ " <-> " ++ show b ++ ")"

instance Show Tableau where
    show = prettyPrintT  

-- Formatear tableau indentado
-- Adaptado de https://stackoverflow.com/a/19442407
prettyPrintT :: Tableau -> String
prettyPrintT t = unlines (prettyPrintAux t)
  where
    prettyPrintAux (Hoja i)       = [show (map lit2f i) ++ if esConsistente i then " O" else " X"]
    prettyPrintAux (Conj l t)     = (show l) : prettyPrintSubTree [t]
    prettyPrintAux (Dis  l t1 t2) = (show l) : prettyPrintSubTree [t1,t2]
    --
    prettyPrintSubTree []     = []
    prettyPrintSubTree [t]    = ((pad "'- " "   ") (prettyPrintAux t))
    prettyPrintSubTree (t:ts) = ((pad "+- " "|  ") (prettyPrintAux t)) ++ prettyPrintSubTree ts
    --
    pad first rest = zipWith (++) (first : repeat rest)
    --
    lit2f (v,b) | b = V v 
                | otherwise = Neg (V v)