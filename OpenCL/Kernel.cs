using System;
using System.Runtime.InteropServices;
using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

public class Kernel : IDisposable
{
	private static nuint[] GLOBAL_WORK_OFFSETS = { 0, 0, 0 };

	private bool disposedValue;

	private IntPtr kernel;

	private IntPtr program;

	private IntPtr command_queue;

	private uint index = 0;

	public Kernel(IntPtr kernel, IntPtr program, IntPtr command_queue)
	{
		this.kernel = kernel;
		this.program = program;
		this.command_queue = command_queue;
	}

	public unsafe void SetArg(nint value)
	{
		Open.CL.GetKernelArgInfo(kernel, index, KernelArgInfo.Name, 0, null, out nuint size);

		nuint actualSize = (nuint)sizeof(nint);

		//                         increment index --v
		if ((ErrorCodes)Open.CL.SetKernelArg(kernel, index, actualSize, value) != ErrorCodes.Success)
			throw new Exception($"Error setting kernel arg (index: {index})");

		++index;
	}

	public nint Run(uint dimensions, nuint[] globalWorkSizes, nuint[] localWorkSizes, nint[] waitEvents)
	{
		// reset the arg index for next run
		index = 0;

		nint waitEvent = nint.Zero;

		ReadOnlySpan<nuint> offsetsSpan = new ReadOnlySpan<nuint>(GLOBAL_WORK_OFFSETS);
		ReadOnlySpan<nuint> globalSpan = new ReadOnlySpan<nuint>(globalWorkSizes);
		ReadOnlySpan<nuint> localSpan = new ReadOnlySpan<nuint>(localWorkSizes);
		ReadOnlySpan<nint> eventsSpan = new ReadOnlySpan<nint>(waitEvents);

		Span<nint> waitEventSpan = new Span<nint>(ref waitEvent);

		int error = Open.CL.EnqueueNdrangeKernel(
			command_queue: command_queue,
			kernel: kernel,
			work_dim: dimensions,
			global_work_offset: offsetsSpan,
			global_work_size: globalSpan,
			local_work_size: localSpan,
			num_events_in_wait_list: (uint)waitEvents.Length,
			event_wait_list: eventsSpan,
			@event: waitEventSpan);

		ErrorCodes _error = (ErrorCodes)error;

		if (ErrorCodes.Success != _error)
			throw new Exception($"Could not enqueue kernel ({_error})");

		return waitEvent;
	}

	#region Implementing IDisposable

	protected virtual void Dispose(bool disposing)
	{
		if (!disposedValue)
		{
			if (disposing)
			{
				int error = Open.CL.ReleaseKernel(kernel);

				if ((ErrorCodes)error != ErrorCodes.Success)
					throw new Exception("Could not release gamma correction kernel");

				error = Open.CL.ReleaseProgram(program);

				if ((ErrorCodes)error != ErrorCodes.Success)
					throw new Exception("Could not release gamma correction kernel");

				kernel = IntPtr.Zero;
				program = IntPtr.Zero;
			}

			// TODO: free unmanaged resources (unmanaged objects) and override finalizer
			disposedValue = true;
		}
	}

	~Kernel()
	{
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