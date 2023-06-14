using System.Numerics;
using OpenCL_Secp256k1.OpenCL;
using OpenCL_Secp256k1.OpenCL.Kernels;
using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.Test;

public static class Secp256k1_Int128_Tests
{
	public static void RunTests(nint device, nint context, nint command_queue)
	{
		// Create our kernel (the actual opencl kernel in contained in this KernelBase class)
		Secp256k1_Tests kernel = new Secp256k1_Tests(device: device, context: context, command_queue: command_queue);


		// Run our tests
		MultiplyTestNeg(kernel, device, context, command_queue);
	}

	private static void MultiplyTest(Secp256k1_Tests kernel, nint device, nint context, nint command_queue)
	{
		uint BUFFER_SIZE = 16;

		// Create a buffer. In CSharp we have to pin (so it wont move in memory) only then can we get a pointer to our data
		byte[] _input = new byte[BUFFER_SIZE];
		byte[] _output = new byte[BUFFER_SIZE];

		CLBuffer input = new CLBuffer(context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, BUFFER_SIZE);
		CLBuffer output = new CLBuffer(context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, BUFFER_SIZE);

		// Setup some test data
		long a = 1234567890123456789;
		ulong b = ulong.MaxValue;

		// Add setup data to the input buffer
		Array.Copy(BitConverter.GetBytes(a), 0, _input, 8, 8);
		Array.Copy(BitConverter.GetBytes(b), 0, _input, 0, 8);

		input.Write(command_queue, _input);

		// Verify with BitInteger
		BigInteger bigA = new BigInteger(a);
		BigInteger bigB = new BigInteger(b);
		BigInteger big16 = new BigInteger(16);
		BigInteger bigResult = (bigA * bigB) + (bigA * bigB) + big16;

		// Do the calculation in OpenCL
		nint waitEvent = kernel.Run(input, output, 1);

		// Wait for the calculation to finish
		OpenCLSharp.WaitForEvent(ref waitEvent);

		output.Read(command_queue, ref _output);

		// Get the result from the output buffer
		ReadOnlySpan<byte> result = new ReadOnlySpan<byte>(_output, 0, 16);
		BigInteger openCLResult = new BigInteger(result, false, !BitConverter.IsLittleEndian);


		string hexStringA = bigA.ToString("X");
		Console.WriteLine("\n\nA: " + hexStringA);

		string hexStringB = bigB.ToString("X");
		Console.WriteLine("B: " + hexStringB + "\n\n");


		string hexStringOpenCL = openCLResult.ToString("X");
		Console.WriteLine("OpenCL Result: " + hexStringOpenCL);

		string hexString = bigResult.ToString("X");
		Console.WriteLine("BigInt Result: " + hexString);
	}

	private static void MultiplyTestNeg(Secp256k1_Tests kernel, nint device, nint context, nint command_queue)
	{
		uint BUFFER_SIZE = 16;

		// Create a buffer. In CSharp we have to pin (so it wont move in memory) only then can we get a pointer to our data
		byte[] _input = new byte[BUFFER_SIZE];
		byte[] _output = new byte[BUFFER_SIZE];

		CLBuffer input = new CLBuffer(context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, BUFFER_SIZE);
		CLBuffer output = new CLBuffer(context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, BUFFER_SIZE);

		// Setup some test data

		// Going to multiply these two long numbers to get a 128bit number
		long a = -1234567890123456789;
		long b = long.MaxValue;

		// Add setup data to the input buffer
		Array.Copy(BitConverter.GetBytes(a), 0, _input, 8, 8);
		Array.Copy(BitConverter.GetBytes(b), 0, _input, 0, 8);

		input.Write(command_queue, _input);

		// Verify with BitInteger
		BigInteger bigA = new BigInteger(a);
		BigInteger bigB = new BigInteger(b);
		BigInteger big16 = new BigInteger(16);
		BigInteger bigResult = (bigA * bigB) + (bigA * bigB) + big16;

		// Do the calculation in OpenCL
		nint waitEvent = kernel.Run(input, output, 1);

		// Wait for the calculation to finish
		OpenCLSharp.WaitForEvent(ref waitEvent);

		output.Read(command_queue, ref _output);

		// Get the result from the output buffer
		ReadOnlySpan<byte> result = new ReadOnlySpan<byte>(_output, 0, 16);
		BigInteger openCLResult = new BigInteger(result, false, !BitConverter.IsLittleEndian);


		string hexStringA = bigA.ToString("X");
		Console.WriteLine("\n\nA: " + hexStringA);

		string hexStringB = bigB.ToString("X");
		Console.WriteLine("B: " + hexStringB + "\n\n");


		string hexStringOpenCL = openCLResult.ToString("X");
		Console.WriteLine("OpenCL Result: " + hexStringOpenCL);

		string hexString = bigResult.ToString("X");
		Console.WriteLine("BigInt Result: " + hexString);
	}
}