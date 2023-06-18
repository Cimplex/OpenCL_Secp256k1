using OpenCL_Secp256k1.OpenCL;

namespace OpenCL_Secp256k1.OpenCL.Kernels;

public class Secp256k1_Verify : KernelBase, IDisposable
{
	private Kernel? _kernel;

	public override (string, string)[] KernelPaths => new[]
	{
		("run_secp256k1_ecdsa_verify", "OpenCL_Secp256k1.OpenCL.Kernels.secp256k1_verify2.cl"),
		("secp256k1_int128_test_mul", "OpenCL_Secp256k1.OpenCL.Kernels.secp256k1_int128_tests.cl"),
	};

	protected override KernelLibrary KernelLibrary { get; init; }

	public Secp256k1_Verify(nint device, nint context, nint command_queue)
	{
		// This is a helper class that lets us load kernels from our resources
		KernelLibrary = CreateKernelLibrary();

		_kernel = KernelLibrary.CreateKernel(command_queue, device, context, "run_secp256k1_ecdsa_verify");
	}

	public nint Run(nint messages, nint public_keys, nint signatures, nint results, int length, nint[]? waitEvents = null)
	{
		if (_kernel is null)
			throw new Exception("Create the kernel before running");

		_kernel.SetArg(messages);
		_kernel.SetArg(public_keys);
		_kernel.SetArg(signatures);
		_kernel.SetArg(results);

		GlobalWorkSize[0] = (nuint)length;

		return _kernel.Run(1, GlobalWorkSize, LocalWorkSize, waitEvents ?? Array.Empty<nint>());
	}

	#region Implementing IDisposable

	private bool disposedValue;

	protected virtual void Dispose(bool disposing)
	{
		if (!disposedValue)
		{
			if (disposing)
			{
				// TODO: dispose managed state (managed objects)
				_kernel?.Dispose();
				_kernel = null;
			}

			// TODO: free unmanaged resources (unmanaged objects) and override finalizer
			// TODO: set large fields to null
			disposedValue = true;
		}
	}

	// // TODO: override finalizer only if 'Dispose(bool disposing)' has code to free unmanaged resources
	// ~Secp256k1_Verify()
	// {
	//     // Do not change this code. Put cleanup code in 'Dispose(bool disposing)' method
	//     Dispose(disposing: false);
	// }

	public void Dispose()
	{
		// Do not change this code. Put cleanup code in 'Dispose(bool disposing)' method
		Dispose(disposing: true);
		GC.SuppressFinalize(this);
	}

	#endregion Implementing IDisposable
}
