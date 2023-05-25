using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

[Flags]
public enum DeviceTypes : ulong
{
	None = DeviceType.None,
	Default = DeviceType.Default,
	Cpu = DeviceType.Cpu,
	Gpu = DeviceType.Gpu,
	Accelerator = DeviceType.Accelerator,
	All = DeviceType.All,
	Custom = DeviceType.Custom
};
