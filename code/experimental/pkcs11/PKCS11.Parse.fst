module PKCS11.Parse


module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open PKCS11.TypeDeclaration
open PKCS11.Attribute
open PKCS11.Mechanism
open PKCS11.Exception
open PKCS11.DateTime
open PKCS11.Cast

open FStar.Option

(*)
assume val parseAttributeDerive: attr_r: _CK_ATTRIBUTE -> 
	Tot (result (attr: attribute_t{attributeGetTypeID attr = attributeRawGetTypeID attr_r /\ 
		(let f = (function| Derive _ _ _ _ -> True | _ -> False) in f attr)
		}
	)
)
*)
val parseAttribute: attr_r: _CK_ATTRIBUTE -> 
	StackInline (result (attr: attribute_t(*{attributeGetTypeID attr = attributeRawGetTypeID attr_r})*)))
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let parseAttribute attr_r = 
	let typ = attributeRawGetTypeID attr_r in 
	let data = attributeRawGetData attr_r in 
	let length = attributeRawGetLength attr_r in 
	let isReadOnly = (*cryptoKiAttributesIsReadOnly typ *) false in 
	if (UInt32.v typ) = 0 then 
			let pointer = castToUlong data in 
			let length = changeSizeOfBuffer length in 
			let attr = CKA_CLASS typ pointer length (attributesIsReadOnly typ) in 
			Inl (attr) 
		else
			(*(CKA_CLASS typ pointer length (attributesIsReadOnly typ)) *)
	(*| 1 -> let data = (if length = 0 then None else Some data) in 
			let attribute = ID typ data length isReadOnly in
				Inl attribute
	| 2 -> let data = Some Seq.createEmpty(*(if length = 0 then None else Some (parseDate data))*) in 
				let attribute = CKA_PRIVATE typ data length isReadOnly in
					Inl attribute
	| 4 -> let data = (if length = 0 then None else Some (bytesToBoolean data length)) in 
				let attribute = Derive typ data length isReadOnly in 
					Inl attribute *) 
	 Inr (TestExc) (*In *)


assume val _parseAttributes: attr_r : buffer _CK_ATTRIBUTE ->s: buffer attribute_t ->  Tot (result (buffer attribute_t))

(*let rec _parseAttributes attr_r s= 
	match  attr_r with
	| hd::tl -> let attribute = parseAttribute hd in 
				if resultIsOk attribute then 
					let attribute = resultLeft attribute in 
						(*(_parseAttributes tl (append s [attribute])) *) 
				else		
					Inr TestExc
	| _ -> Inl s
*)
assume val parseAttributes: attr_r: buffer _CK_ATTRIBUTE -> Tot (result (buffer attribute_t))

(*let parseAttributes attr_r = 
	_parseAttributes attr_r	[]
*)


assume val rng_algorithm: input: buffer FStar.UInt8.t ->  length: FStar.UInt32.t -> 
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

assume val rng_algorithm2: input: buffer FStar.UInt8.t ->  length: FStar.UInt32.t -> 
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))    

val parseMechanism: m: _CK_MECHANISM-> b: buffer _CK_ULONG-> 
	len: FStar.UInt32.t{length b == UInt32.v len} -> StackInline (result mechanism)
		(requires (fun h -> True))
	    (ensures (fun h0 _ h1 -> True)) 

let parseMechanism m b len = 
	let id = mechanismRawGetTypeID m in 
	let params = getMechanismRawParameters m in 
	let paramLen = getMechanismRawParametersLen m in 
	if (UInt32.v id) = 1 then 
		let lengthProvidedAttr = 3ul in 
		let lengthRequiredAttr = 10ul in 
		let idForProvidedAttributes = id in 
		
		let idForRequiredAttributes = id in 
		let requiredAttrs = getMemoryIndexForMechanism idForRequiredAttributes b len in 

		let idForProvidedAttributes = id in 
		let requestedProvidedAttributes = getMemoryIndexForMechanism idForProvidedAttributes b len in 
		let attr = CKA_CLASS 0ul requestedProvidedAttributes 2ul false in 
		
		//let stubForAttributes = getAddressOfMechanismAttributes m in 
		
		let bufferForAttributes = create attr 3ul in 
		Inl 
			(Generation id rng_algorithm params paramLen bufferForAttributes 
			1ul requiredAttrs 10ul)
	else
		Inr (TestExc)		
	
