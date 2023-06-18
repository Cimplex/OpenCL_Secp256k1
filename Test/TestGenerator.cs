using OpenCL_Secp256k1.OpenCL;
using Secp256k1Net;

namespace OpenCL_Secp256k1.Test;

public class TestGenerator
{
	private static Secp256k1 _secp256k1 = new Secp256k1();

	public List<byte[]> PublicKeyList = new List<byte[]>();
	public List<byte[]> MessageHashList = new List<byte[]>();
	public List<byte[]> SignatureList = new List<byte[]>();

	public void GenerateAddKeyHashSig()
	{
		// Create a Private Key, Derive Public Key, Generate Message Hash, Sign Message Hash... and i guess verify signature

		var privateKey = new byte[Secp256k1.PRIVKEY_LENGTH];
		var rnd = System.Security.Cryptography.RandomNumberGenerator.Create();
		do { rnd.GetBytes(privateKey); }

		while (!_secp256k1.SecretKeyVerify(privateKey));

		var publicKey = new byte[Secp256k1.PUBKEY_LENGTH];
		
		if ( ! _secp256k1.PublicKeyCreate(publicKey, privateKey)) throw new Exception("Could not derive public key");
		
		
		var keypair = new { PrivateKey = privateKey, PublicKey = publicKey };
		var msgBytes = System.Text.Encoding.UTF8.GetBytes("Hello!!");
		var msgHash = System.Security.Cryptography.SHA256.HashData(msgBytes);
		if (Secp256k1.HASH_LENGTH != msgHash.Length) Utilities.error("Wrong Size");
		var signature = new byte[Secp256k1.SIGNATURE_LENGTH];
		if ( ! _secp256k1.Sign(signature, msgHash, keypair.PrivateKey)) Utilities.error("Could not create signature");
		bool verified = _secp256k1.Verify(signature, msgHash, keypair.PublicKey);

		PublicKeyList.Add(publicKey);
		MessageHashList.Add(msgHash);
		SignatureList.Add(signature);
	}
}