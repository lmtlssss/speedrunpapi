import cbor from 'cbor';
import {createHash, createPublicKey, verify as edVerify} from 'node:crypto';
import {readFileSync} from 'node:fs';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';

const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const dir=resolve(root,'vectors');
const sha=x=>createHash('sha256').update(x).digest();
const enc=x=>cbor.Encoder.encodeAsync(x,{canonical:true});
const reject=(ok,message)=>{if(!ok)throw Error(message)};
const eq=(a,b)=>Buffer.from(a).equals(Buffer.from(b));
const key64=readFileSync(resolve(root,'test-public-key.base64'),'utf8').trim();
const publicDer=Buffer.concat([Buffer.from('302a300506032b6570032100','hex'),
  Buffer.from(key64,'base64')]);
const key=createPublicKey({key:publicDer,format:'der',type:'spki'});

const compose=(a,b)=>{
  const [f,g,u,v,w]=a,[h,k,p,q,r]=b;
  return [h*f,h*g+k,u+p*f*f,v+2*p*f*g+q*f,w+p*g*g+q*g+r];
};
function checkMath(predicate,source,evidence,verdict){
  const name=predicate.split(':')[2];
  if(name==='finite-trace-preservation'){
    reject(verdict==='certified','trace verdict');
    const {states,inputs,pi,next,observations,reduced_next,reduced_observations}=source;
    reject(pi.length===states.length && new Set(pi).size===reduced_next.length
      && new Set(pi).has(0) && new Set(pi).has(reduced_next.length-1),'surjection');
    let count=0;
    for(let s=0;s<states.length;s++)for(let u=0;u<inputs.length;u++){
      reject(pi[next[s][u]]===reduced_next[pi[s]][u],'transition');
      reject(observations[s][u]===reduced_observations[pi[s]][u],'observation');
      count++;
    }
    reject(evidence.checked_pairs===count && evidence.finite_trace_preserved===true,
      'trace evidence');
  }else if(name==='affine-cost-composition'){
    reject(verdict==='certified' && source.intervals.length===3,'affine domain');
    const [a,b,c]=source.intervals;
    const lhs=compose(compose(a,b),c), rhs=compose(a,compose(b,c));
    reject(JSON.stringify(lhs)===JSON.stringify(rhs),'associativity');
    reject(evidence.associative===true && JSON.stringify(lhs)===
      JSON.stringify(evidence.composed),'composed evidence');
  }else if(name==='output-uniqueness' || name==='witness-uniqueness'){
    const fibers=source.fibers;
    const oc=fibers.map(x=>new Set(x.witnesses.map(w=>w.output)).size);
    const wc=fibers.map(x=>x.witnesses.length);
    if(name==='output-uniqueness'){
      reject(verdict==='certified' && oc.every(x=>x===1),'output unique');
      reject(JSON.stringify(evidence.output_counts)===JSON.stringify(oc)
       && JSON.stringify(evidence.witness_counts)===JSON.stringify(wc),'counts');
    } else {
      const n=wc.findIndex(x=>x>1);
      reject(verdict==='broken'&&n>=0,'witness verdict');
      reject(evidence.input===fibers[n].input &&
        JSON.stringify(evidence.witness_ids)===
        JSON.stringify(fibers[n].witnesses.map(w=>w.id)),'witness evidence');
    }
  } else throw Error('unregistered predicate');
}
async function verifyRecord(raw,art,ev){
  const outer=cbor.decodeFirstSync(raw);
  reject(outer instanceof cbor.Tagged && outer.tag===18,'COSE tag');
  reject(eq(await enc(outer),raw),'COSE deterministic encoding');
  const [protectedBytes,unprotected,payloadBytes,signature]=outer.value;
  reject(outer.value.length===4 && unprotected &&
    Object.keys(unprotected).length===0 && Buffer.isBuffer(signature) &&
    signature.length===64,'COSE shape');
  const head=cbor.decodeFirstSync(protectedBytes);
  reject(eq(await enc(head),protectedBytes),'protected encoding');
  reject(head.get(1)===-8&&head.get(3)==='application/cbor' &&
    eq(head.get(4),Buffer.from('taa-interop-test-01')) &&
    head.get(15).get(1)==='urn:taa:interop:issuer:test-only' &&
    head.get(15).get(2)==='urn:taa:interop:artifact','issuer header');
  const payload=cbor.decodeFirstSync(payloadBytes);
  reject(eq(await enc(payload),payloadBytes),'payload encoding');
  reject(payload.size===6 && payload.get(1)==='taa.exact-computation-claim.v1',
    'profile');
  const sigStructure=await enc(['Signature1',protectedBytes,Buffer.alloc(0),payloadBytes]);
  reject(edVerify(null,sigStructure,key,signature),'Ed25519 signature');
  const artifact=payload.get(2),claim=payload.get(3),
    verifier=payload.get(4),evidence=payload.get(5);
  reject(artifact.get(1)==='sha-256' && eq(artifact.get(2),sha(art)) &&
    artifact.get(3)==='application/json','source bytes');
  reject(verifier.get(1)==='taa-reference-python-independent' &&
    verifier.get(2)==='1.0.0' && verifier.get(3)==='sha-256' &&
    eq(verifier.get(4),sha(readFileSync(resolve(root,'python/verify.py')))),
    'verifier digest');
  reject(evidence.get(1)==='sha-256' && eq(evidence.get(2),sha(ev)) &&
    evidence.get(4)==='application/json','evidence bytes');
  reject(claim.get(2)==='finite-exact-domain' &&
    claim.get(4)==='full-domain-check'&&claim.get(5).length===0,
    'claim scope');
  checkMath(claim.get(1),JSON.parse(art),JSON.parse(ev),claim.get(3));
  return {predicate:claim.get(1),verdict:claim.get(3)};
}
const manifest=JSON.parse(readFileSync(resolve(dir,'manifest.json')));
let positive=0,negative=0,python=0;
for(const item of manifest.vectors){
 const src=readFileSync(resolve(dir,item.artifact));
 const ev=readFileSync(resolve(dir,item.evidence));
 const raw=readFileSync(resolve(dir,item.cose));
 const result=await verifyRecord(raw,src,ev);
 reject(result.predicate===item.predicate && result.verdict===item.verdict,
  'manifest');
 positive++;
 for(const [altered,s,e] of [
  [Buffer.concat([raw.subarray(0,-1),Buffer.from([raw.at(-1)^1])]),src,ev],
  [raw,Buffer.concat([src,Buffer.from(' ')]),ev],
  [raw,src,Buffer.concat([ev,Buffer.from(' ')])],
  [Buffer.concat([Buffer.from([0]),raw.subarray(1)]),src,ev]
 ]){
  try{await verifyRecord(altered,s,e);throw Error('accepted tampering')}
  catch(error){if(error.message==='accepted tampering')throw error;negative++}
 }
 const round=readFileSync(resolve(dir,item.name+'.python.cose'));
 await verifyRecord(round,src,ev);
 python++;
}
console.log(JSON.stringify({node_verified:positive,python_signed_verified:python,
  negative_rejections:negative}));
