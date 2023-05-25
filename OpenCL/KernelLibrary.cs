using System;
using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL
{
    public class KernelLibrary
    {
        public string[] Names { get; private set; } = Array.Empty<string>();

        public uint[] Lengths { get; private set; } = Array.Empty<uint>();

        public char[][] Sources { get; private set; } = Array.Empty<char[]>();

        public KernelLibrary(string[] names, char[][] sources, uint[] lengths)
        {
            Names = names;
            Sources = sources;
            Lengths = lengths;
        }

        private (char[] source, uint length) GetSourceFromName(string name)
        {
            try
            {
                for (int i = 0; i < Names.Length; i += 1)
                    if (Names[i] == name)
                        return ( Sources[i], Lengths[i] );
            }
            catch { }

            throw new Exception(string.Format("Cannot find embedded resource from name: '{0}'", name));
        }

        public unsafe Kernel CreateKernel(nint command_queue, nint device, nint context, string kernelName)
        {
            IntPtr program = IntPtr.Zero;
            IntPtr kernel = IntPtr.Zero;

            (char[] source, uint length) = GetSourceFromName(kernelName);

			Console.WriteLine($"Creating kernel '{kernelName}'");
			Console.WriteLine($"Source length: {length}");
			Console.WriteLine($"Source: {new string(source)}");

            // TODO: Can we get rid of these allocations?
            byte[] bytes = Array.ConvertAll<char, byte>(source, c => (byte)c);

            byte*[] byteSpan = new byte*[1];
            nuint[] lengths = new nuint[] { (nuint)source.Length };

            fixed (byte* ptr = &bytes[0])
            {
                byteSpan[0] = ptr;
                fixed (byte** row = &byteSpan[0])
                fixed (nuint* lengthPtr = &lengths[0])
                {
                    program = Open.CL.CreateProgramWithSource(
                        context: context,
                        count: 1u,
                        strings: row,
                        lengths: lengthPtr,
                        errcode_ret: out int errorCode);

                    if ((ErrorCodes)errorCode != ErrorCodes.Success)
                        throw new Exception($"Could not create program from source. OpenCL Error: {(ErrorCodes)errorCode}");
                }
            }

            ReadOnlySpan<nint> devices = new ReadOnlySpan<nint>(device);

            int error = Open.CL.BuildProgram(program, 1u, devices, string.Empty, null, null);

            if ((ErrorCodes)error != ErrorCodes.Success)
                throw new Exception($"Could not build program: {(ErrorCodes)error}");

            Span<int> errorSpan = new Span<int>(ref error);
            kernel = Open.CL.CreateKernel(program, kernelName, errorSpan);

            if ((ErrorCodes)error != ErrorCodes.Success)
                throw new Exception($"Could not create kernel: {(ErrorCodes)error}");

            return new Kernel(command_queue, program, kernel);
        }
    }
}

