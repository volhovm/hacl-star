module QTesla.Params

open Lib.IntTypes

let params_lambda = 160 // security parameter
let params_kappa = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n = 2048 // Dimension
let params_k = 5       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q = 1129725953 // modulus
let params_h = 40      // # of nonzero entries of output elements of Enc
let params_Le = 901    // bound on e_i for checkE
let params_Ls = 901    // bound on s for checkS
let params_B = 8388607 // interval the randomness is chosing from during signing
let params_d = 24      // number of rounded bits
let params_bGenA = 180 // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168
let params_xof = Spec.SHA3.shake128        // extendable output function used in PRF1: use shake128 or shake256 depending on parameters chosen
let params_hash_shake = Spec.SHA3.shake128 // hash function used in hash H: use shake128 or shake256 depending on parameters chosen

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 752833504
let computed_omega = 905348506
let computed_phi_inv = 500168718
let computed_omega_inv = 224686349
let computed_n_inv = 1129174329
