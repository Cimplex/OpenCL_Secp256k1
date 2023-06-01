using System.Runtime.InteropServices;
using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

public class CLBuffer : IDisposable
{
	private nint _context;

	public uint Size { get; private set; }

	private nint device_pointer;

	public CLBuffer(nint context, MemFlags flags, uint bufferSize)
	{
		_context = context;
		Size = bufferSize;

		int error = 0;
		Span<int> error_span = new Span<int>(ref error);

		device_pointer = Open.CL.CreateBuffer<nint>(context, flags, (nuint)bufferSize, null, error_span);
	}

	public unsafe void Write(nint command_queue, byte[] buffer)
	{
		if (buffer.Length != Size)
			throw new Exception("Buffer is not the same size.");

		
		GCHandle host_handle = GCHandle.Alloc(buffer, GCHandleType.Pinned);

		nint wait_event = 0;
		Span<nint> wait_event_span = new Span<nint>(ref wait_event);

		ErrorCodes error = (ErrorCodes)Open.CL.EnqueueWriteBuffer(command_queue, device_pointer, true, 0, (nuint)buffer.Length, host_handle.AddrOfPinnedObject().ToPointer(), 0, (ReadOnlySpan<nint>)null, wait_event_span);

		if ((ErrorCodes)error != ErrorCodes.Success)
			throw new Exception($"Cannot write buffer. OpenCL Error: {(ErrorCodes)error}");

		host_handle.Free();
	}

	public unsafe void Read(nint command_queue, ref byte[] buffer)
	{
		if (buffer.Length != Size)
			throw new Exception("Buffer is not the same size.");

		
		GCHandle host_handle = GCHandle.Alloc(buffer, GCHandleType.Pinned);

		nint wait_event = 0;
		Span<nint> wait_event_span = new Span<nint>(ref wait_event);

		ErrorCodes error = (ErrorCodes)Open.CL.EnqueueReadBuffer(command_queue, device_pointer, true, 0, (nuint)buffer.Length, host_handle.AddrOfPinnedObject().ToPointer(), 0, (ReadOnlySpan<nint>)null, wait_event_span);

		if ((ErrorCodes)error != ErrorCodes.Success)
			throw new Exception($"Cannot write buffer. OpenCL Error: {(ErrorCodes)error}");

		host_handle.Free();
	}

	public static implicit operator nint(CLBuffer buffer) => buffer.device_pointer;

	#region Implementing IDisposable

	private bool disposedValue;

	protected virtual void Dispose(bool disposing)
	{
		if (!disposedValue)
		{
			if (disposing)
			{
				// TODO: dispose managed state (managed objects)
			}

			// TODO: free unmanaged resources (unmanaged objects) and override finalizer
			// TODO: set large fields to null
			ErrorCodes error = (ErrorCodes)Open.CL.ReleaseMemObject(device_pointer);

			if (error != ErrorCodes.Success)
				throw new Exception("Could not release memory object.");

			device_pointer = nint.Zero;

			disposedValue = true;
		}
	}

	// TODO: override finalizer only if 'Dispose(bool disposing)' has code to free unmanaged resources
	~CLBuffer()
	{
		// Do not change this code. Put cleanup code in 'Dispose(bool disposing)' method
		Dispose(disposing: false);
	}

	public void Dispose()
	{
		// Do not change this code. Put cleanup code in 'Dispose(bool disposing)' method
		Dispose(disposing: true);
		GC.SuppressFinalize(this);
	}

	#endregion Implementing IDisposable
}