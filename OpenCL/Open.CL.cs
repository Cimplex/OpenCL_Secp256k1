using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

public static class Open
{
	public static CL CL { get; }

	static Open() => CL = CL.GetApi();
}