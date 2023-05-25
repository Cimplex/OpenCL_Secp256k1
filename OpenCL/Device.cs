using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

public class Device
{
	public IntPtr Handle { get; }

	public string Name { get; }

	public string ExtensionSupport { get; }

	public ulong GlobalMemory { get; }

	public int WorkGroupSize { get; }

	public DeviceTypes DeviceType { get; }

	public bool IsValid { get; }

	public Device(IntPtr device)
	{
		IsValid = false;

		Name = "Invalid Device";
		ExtensionSupport = "Invalid Device";
		Handle = device;

		try
		{
			Name = Utilities.GetDeviceInfo_String(device, DeviceInfo.Name);
			DeviceType = (DeviceTypes)Utilities.GetDeviceInfo_UInt64(device, DeviceInfo.Type);
			GlobalMemory = Utilities.GetDeviceInfo_UInt64(device, DeviceInfo.GlobalMemSize);
			WorkGroupSize = Utilities.GetDeviceInfo_Int32(device, DeviceInfo.MaxWorkGroupSize);
			ExtensionSupport = Utilities.GetDeviceInfo_String(device, DeviceInfo.Extensions);

			IsValid = true;
		}
		catch (Exception e)
		{
#if DEBUG
			Console.WriteLine($"Error querying device: {e.Message}");
#endif
		}
	}

	public static implicit operator IntPtr(Device d) => d.Handle;
}
