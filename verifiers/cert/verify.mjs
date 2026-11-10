#!/usr/bin/env node
// Offline signature and source-binding verification for the published Colony Ed25519 key.
// A live revocation/status response is checked when supplied by the registry endpoint.
import fs from 'node:fs';
import { createHash, createPublicKey, verify } from 'node:crypto';

const PUBLIC_KEY_SPKI = 'MCowBQYDK2VwAyEArlrZBZVGOIsXaBmm34C7mF/I84XktT3Nsc/3bl2amvY=';
const KEY_ID = 'colony-ed25519-20261108';
function canonical(cert) {
  return JSON.stringify({
    id:cert.id, result:cert.result, family:cert.family, domain:cert.domain,
    scope:cert.scope, gadget_id:cert.gadget_id ?? null, checksum:cert.checksum ?? null,
    issued_at:cert.issued_at, issuer:cert.issuer, public:cert.public, mark:cert.mark,
    signature_algorithm:cert.signature_algorithm, key_id:cert.key_id
  });
}
const [certificatePath, sourcePath] = process.argv.slice(2);
if (!certificatePath || !sourcePath) {
  console.error('Usage: node verify.mjs <certificate.json> <original-source-file>');
  process.exit(2);
}
const response = JSON.parse(fs.readFileSync(certificatePath,'utf8'));
const cert = response.certificate ?? response;
if (cert.signature_algorithm !== 'Ed25519' || cert.key_id !== KEY_ID ||
    typeof cert.signature !== 'string' || !/^[A-Za-z0-9+/]{86}==$/.test(cert.signature)) {
  throw new Error('Certificate is missing a supported Ed25519 signature');
}
const source = fs.readFileSync(sourcePath);
const checksum = 'sha256:' + createHash('sha256').update(source).digest('hex');
if (cert.checksum !== checksum) throw new Error('Certificate source checksum differs from file');
if (cert.result !== 'Certified') throw new Error('Certificate does not certify this source');
if (response.revoked || response.status === 'revoked' || response.active === false) {
  throw new Error('Certificate has been revoked');
}
const pub = createPublicKey({key:Buffer.from(PUBLIC_KEY_SPKI,'base64'),format:'der',type:'spki'});
if (!verify(null, Buffer.from(canonical(cert)), pub, Buffer.from(cert.signature,'base64'))) {
  throw new Error('Ed25519 signature check failed');
}
console.log(JSON.stringify({ok:true,cert_id:cert.id,key_id:KEY_ID,checksum}));
