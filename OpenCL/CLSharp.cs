// This class is to hide some of the ugly details of the OpenCL API with csharp.
// Its pretty straight forward if you ignore the Span<> stuff.
// Its a necessary evil to avoid using unsafe code as much as possible
// In some other areas, I do use unsafe, but only because I'm lazy...
// Lets keep this simple!

using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

public static class OpenCLSharp
{
	public static nint CreateContext(Device device)
	{
		// Make sure to use the Handle... facepalm
		ReadOnlySpan<nint> devicesSpan = new ReadOnlySpan<nint>(device.Handle);

		int error = 0;
		Span<int> errorSpan = new Span<int>(ref error);
		ReadOnlySpan<nint> properties = new ReadOnlySpan<nint>();
		Span<nint> user_data = new Span<nint>();

		nint Context = Open.CL.CreateContext<nint>(properties, 1u, devicesSpan, null, user_data, errorSpan);

		if ((ErrorCodes)error != ErrorCodes.Success)
			throw new Exception($"Cannot create Context. OpenCL Error: {(ErrorCodes)error}");

		return Context;
	}

	public static nint CreateCommandQueue(nint Context, Device Device)
	{
		int error = 0;
		Span<int> errorSpan = new Span<int>(ref error);

		nint CommandQueue = Open.CL.CreateCommandQueue(Context, Device.Handle, CommandQueueProperties.None, out error);

		if ((ErrorCodes)error != ErrorCodes.Success)
			throw new Exception($"Cannot create CommandQueue. OpenCL Error: {(ErrorCodes)error}");

		return CommandQueue;
	}

	
}