module Levels where

import Common

data Level = Omega | Omega1 | LZ | LS Level | LMax Level Level | LVar Ix

instance Show Level where
  show Omega = "omega"
  show Omega1 = "omega1"
  show LZ = "LZ"
  show (LS l) = "(LS " ++ show l ++ ")"
  show (LMax a b) = "(max " ++ show a ++ " " ++ show b ++ ")"
  show (LVar x) = "'" ++ show x

data VLevel
  = VOmega
  | VOmega1
  | VLZ
  | VLS VLevel
  | VLMax VLevel VLevel
  | VLVar Lvl
  deriving (Show, Eq)

type EnvLevel = [VLevel]

evalLevel :: EnvLevel -> Level -> VLevel
evalLevel e l = case l of
  LVar i -> e !! i
  Omega -> VOmega
  Omega1 -> VOmega1
  LZ -> VLZ
  LS l -> vls (evalLevel e l)
  LMax a b -> vlmax (evalLevel e a) (evalLevel e b)

vls :: VLevel -> VLevel
vls VOmega = VOmega1
vls l = VLS l

vlmax :: VLevel -> VLevel -> VLevel
vlmax VOmega1 _ = VOmega1
vlmax _ VOmega1 = VOmega1
vlmax v@(VLVar x) (VLVar y) | x == y = v
vlmax x@(VLVar _) y = VLMax x y
vlmax y x@(VLVar _) = VLMax x y
vlmax VLZ a = a
vlmax a VLZ = a
vlmax (VLS a) (VLS b) = vlmax a b
vlmax a b = VLMax a b

quoteLevel :: Lvl -> VLevel -> Level
quoteLevel k l = case l of
  VLVar l -> LVar (k - l - 1)
  VOmega -> Omega
  VOmega1 -> Omega1
  VLZ -> LZ
  VLS l -> LS (quoteLevel k l)
  VLMax a b -> LMax (quoteLevel k a) (quoteLevel k b)

nfLevel :: Level -> Level
nfLevel = quoteLevel 0 . evalLevel []

convLevel :: VLevel -> VLevel -> Bool
convLevel a b = case (a, b) of
  (VLS a, VLS b) -> convLevel a b
  (VLMax a b, VLMax c d) -> convLevel a c && convLevel b d
  (a, b) -> a == b
