import cbor from 'cbor';
import { createHash, createPrivateKey, createPublicKey, sign } from 'node:crypto';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const dir = resolve(root, 'vectors');
mkdirSync(dir, { recursive: true });
const sha = value => createHash('sha256').update(value).digest();
const canonical = value => cbor.Encoder.encodeAsync(value, {canonical:true});
const seed = Buffer.from(Array.from({length:32}, (_, i) => i));
const priv = createPrivateKey({
  key: Buffer.concat([Buffer.from('302e020100300506032b657004220420','hex'), seed]),
  format: 'der', type: 'pkcs8'
});
const pub = createPublicKey(priv).export({format:'der',type:'spki'}).subarray(-32);
writeFileSync(resolve(root, 'test-public-key.base64'), pub.toString('base64') + '\n');
const issuer = 'urn:taa:interop:issuer:test-only';
const header = new Map([[1,-8],[3,'application/cbor'],
  [4,Buffer.from('taa-interop-test-01')],
  [15,new Map([[1,issuer],[2,'urn:taa:interop:artifact']])]]);
const protectedBytes = await canonical(header);
const sum=(a,b)=>{const [f,g,u,v,w]=a,[h,k,p,q,r]=b;
  return [h*f,h*g+k,u+p*f*f,v+2*p*f*g+q*f,w+p*g*g+q*g+r]};

const finite={states:['A','B','C','D'],inputs:['zero','one'],pi:[0,0,1,1],
 next:[[1,2],[0,3],[3,0],[2,1]],
 observations:[[0,1],[0,1],[1,0],[1,0]],
 reduced_next:[[0,1],[1,0]],
 reduced_observations:[[0,1],[1,0]]};
const affine={intervals:[[2,1,1,0,1],[3,-2,2,3,4],[1,4,3,-1,2]]};
const composed=sum(sum(affine.intervals[0],affine.intervals[1]),affine.intervals[2]);
const relation={fibers:[
  {input:'u0',witnesses:[{id:'w1',output:7},{id:'w2',output:7}]},
  {input:'u1',witnesses:[{id:'w3',output:8}]}
]};
const cases=[
 ['finite-trace','urn:taa:finite-trace-preservation:v1','certified',finite,
  {checked_pairs:8,finite_trace_preserved:true}],
 ['affine-cost','urn:taa:affine-cost-composition:v1','certified',affine,
  {composed,associative:true}],
 ['output-unique','urn:taa:output-uniqueness:v1','certified',relation,
  {output_counts:[1,1],witness_counts:[2,1]}],
 ['witness-nonunique','urn:taa:witness-uniqueness:v1','broken',relation,
  {input:'u0',witness_ids:['w1','w2']}],
];
const verifierDigest = sha(readFileSync(resolve(root,'python/verify.py')));
const records=[];
for(const [name,predicate,verdict,artifact,evidence] of cases) {
  const sourceBytes = Buffer.from(JSON.stringify(artifact)+'\n');
  const evidenceBytes = Buffer.from(JSON.stringify(evidence)+'\n');
  const claim = new Map([[1,predicate],[2,'finite-exact-domain'],
   [3,verdict],[4,'full-domain-check'],[5,[]]]);
  const payload = new Map([
    [1,'taa.exact-computation-claim.v1'],
    [2,new Map([[1,'sha-256'],[2,sha(sourceBytes)],[3,'application/json']])],
    [3,claim],
    [4,new Map([[1,'taa-reference-python-independent'],[2,'1.0.0'],
      [3,'sha-256'],[4,verifierDigest]])],
    [5,new Map([[1,'sha-256'],[2,sha(evidenceBytes)],[4,'application/json']])],
    [6,'2026-11-08T00:00:00Z']
  ]);
  const payloadBytes=await canonical(payload);
  const tbs=await canonical(['Signature1',protectedBytes,Buffer.alloc(0),payloadBytes]);
  const sig=sign(null,tbs,priv);
  const cose=await canonical(new cbor.Tagged(18,[protectedBytes,new Map(),payloadBytes,sig]));
  writeFileSync(resolve(dir,name+'.artifact.json'),sourceBytes);
  writeFileSync(resolve(dir,name+'.evidence.json'),evidenceBytes);
  writeFileSync(resolve(dir,name+'.cose'),cose);
  records.push({name,predicate,verdict,
   cose:name+'.cose',artifact:name+'.artifact.json',
   evidence:name+'.evidence.json',
   sha256_cose:sha(cose).toString('hex')});
}
writeFileSync(resolve(dir,'manifest.json'),JSON.stringify({
  schema:'taa.scitt-interop.v1',test_only:true,issuer,
  protected_header:'COSE_Sign1 EdDSA/Ed25519; CWT iss/sub',
  signed_statement_media_type:'application/scitt-statement+cose',
  receipt_present:false,
  public_key_file:'../test-public-key.base64',
  vectors:records
},null,2)+'\n');
console.log(JSON.stringify({generated:records.length, cases:records.map(x=>x.name)}));
