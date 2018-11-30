module QTesla.Params

open Lib.IntTypes

#reset-options "--max_fuel 0 --max_ifuel 0"

let params_lambda = 95
let params_kappa = 32
let params_n = 512
let params_xi = 27
let params_k = 1
let params_q = 4205569
let params_h = 30
let params_Le = 1586
let params_Ls = 1586
let params_B = 1048575
let params_d = 21
let params_bGenA = 19
let params_rateXOF = 168

let params_prf1 = Spec.SHA3.shake128
let params_prf2 = Spec.SHA3.shake128
let params_genA_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_gaussSampler_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_enc_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_ysampler_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_hashG = Spec.SHA3.shake128
let params_hashH_shake = Spec.SHA3.shake128

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 3768668
let computed_omega = 118029
let computed_phi_inv = 3764481
let computed_omega_inv = 590666
let computed_n_inv = 4197355

// Generated using gaussSigma2Sample_table.magma from the submission package.
let cdt_list: list nat =
  [02000000000000000000000000000000;
   03000000000000000000000000000000;
   03200000000000000000000000000000;
   03210000000000000000000000000000;
   03210200000000000000000000000000;
   03210201000000000000000000000000;
   03210201002000000000000000000000;
   03210201002001000000000000000000;
   03210201002001000200000000000000;
   03210201002001000200010000000000;
   03210201002001000200010000200000;
   03210201002001000200010000200001]
