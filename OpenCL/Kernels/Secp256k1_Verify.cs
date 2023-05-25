using OpenCL_Secp256k1.OpenCL;

namespace OpenCL_Secp256k1.OpenCL.Kernels;

public class Secp256k1_Verify : KernelBase, IDisposable
{
	private Kernel? _kernel;

	public override (string, string)[] KernelPaths => new[]
	{
		("secp256k1_verify", "OpenCL_Secp256k1.OpenCL.Kernels.secp256k1_verify.cl"),
		("secp256k1_int128_test_mul", "OpenCL_Secp256k1.OpenCL.Kernels.secp256k1_int128_tests.cl"),
	};

	protected override KernelLibrary KernelLibrary { get; init; }

	public Secp256k1_Verify(nint command_queue, nint device, nint context)
	{
		// This is a helper class that lets us load kernels from our resources
		KernelLibrary = CreateKernelLibrary();

		_kernel = KernelLibrary.CreateKernel(command_queue, device, context, "secp256k1_int128_test_mul");
	}

	// Input = ByteArray
	// Output = ByteArray
	// length = Number of pairs of 64bit values
	// Returns OpenCL wait event (nint)
	public nint Run(nint input, nint output, int length, nint[]? waitEvents = null)
	{
		if (_kernel is null)
			throw new Exception("Create the kernel before running");

		_kernel.SetArg(input, (uint)IntPtr.Size);
		_kernel.SetArg(output, (uint)IntPtr.Size);

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
