using OpenCL_Secp256k1.OpenCL;
using OpenCL_Secp256k1.OpenCL.Kernels;
using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.Test;

public class Secp256k1_Test
{
	private readonly nint _device;
	private readonly nint _context;
	private readonly nint _command_queue;

	public Secp256k1_Test(nint device, nint context, nint command_queue)
	{
		_device = device;
		_context = context;
		_command_queue = command_queue;
	}

	public void RunTests()
	{
		uint HASHES = 1;

		// Create a buffers
		// __global uchar* messages, __global uchar* public_keys, __global uchar* signatures, __global uchar* results) {
		byte[] _messages = new byte[HASHES * 32];
		byte[] _public_keys = new byte[HASHES * 64];
		byte[] _signatures = new byte[HASHES * 64];
		byte[] _results = new byte[HASHES * 32];

		// Copy test data to buffers
		TestGenerator gen = new TestGenerator();
		gen.GenerateAddKeyHashSig();
		gen.MessageHashList[0].CopyTo(_messages, 0);
		gen.PublicKeyList[0].CopyTo(_public_keys, 0);
		gen.SignatureList[0].CopyTo(_signatures, 0);

		CLBuffer messages = new CLBuffer(_context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, (uint)_messages.Length);
		CLBuffer public_keys = new CLBuffer(_context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, (uint)_public_keys.Length);
		CLBuffer signatures = new CLBuffer(_context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, (uint)_signatures.Length);
		CLBuffer results = new CLBuffer(_context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, (uint)_results.Length);
		
		messages.Write(_command_queue, _messages);
		public_keys.Write(_command_queue, _public_keys);
		signatures.Write(_command_queue, _signatures);

		Secp256k1_Verify kernel = new Secp256k1_Verify(_device, _context, _command_queue);

		// Do the calculation in OpenCL
		nint waitEvent = kernel.Run(messages, public_keys, signatures, results, (int)HASHES);

		// Wait for the calculation to finish
		OpenCLSharp.WaitForEvent(ref waitEvent);

		results.Read(_command_queue, ref _results);

		Console.Write("OpenCL Result: ");

		for (int i = 0; i < _results.Length - 1; i++)
			Console.Write(_results[i].ToString("X2") + ", ");
		Console.WriteLine(_results[_results.Length - 1].ToString("X2"));
		
	}
};