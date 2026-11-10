#!/usr/bin/env node
/** Standalone verification of self-contained Colony ephemeral LAB evidence. */
import fs from "node:fs";
import path from "node:path";
import {createHash,createPublicKey,verify} from "node:crypto";
const sha=(b)=>"sha256:"+createHash("sha256").update(b).digest("hex");
try{
 const root=path.resolve(process.argv[2]??path.dirname(new URL(import.meta.url).pathname),"");
 const data=fs.readFileSync(path.join(root,"receipt.json"));
 const signature=JSON.parse(fs.readFileSync(path.join(root,"signature.json"),"utf8"));
 if(signature.schema!=="colony.market-lab-signature.v1" ||
    signature.issuer!=="Colony independent local lab, ephemeral key" ||
    signature.signature_scope!=="laboratory observation receipt" ||
    signature.signature_algorithm!=="Ed25519" ||
    signature.production_issuer!==false ||
    signature.real_customer_settlement!==false ||
    sha(data)!==signature.message_digest)throw Error("Scope or receipt hash incorrect");
 const der=Buffer.from(signature.public_key_spki_base64,"base64");
 if(signature.signer_key_id!=="lab-"+sha(der).slice(0,24))throw Error("Signer key id incorrect");
 const pub=createPublicKey({key:der,format:"der",type:"spki"});
 if(!verify(null,data,pub,Buffer.from(signature.signature_base64,"base64")))
     throw Error("Ed25519 LAB signature rejected");
 console.log(JSON.stringify({ok:true,signature:"Ed25519",scope:"ephemeral_local_laboratory_only",
    source_bound:signature.message_digest,production_certificate:false}));
}catch(e){console.error("Invalid lab signature:",e.message);process.exitCode=1}
