using System.Text;
using Silk.NET.OpenCL;
using System.Text.RegularExpressions;

namespace OpenCL_Secp256k1.OpenCL;

public static class Utilities
{
	#region Platform Query Functions

	public unsafe static string GetPlatformInfo(IntPtr platform, PlatformInfo info)
	{
		nuint size = 0;
		
		ErrorCodes result = (ErrorCodes)Open.CL.GetPlatformInfo(platform, info, 0, null, out size);
		if (result != ErrorCodes.Success)
			throw new Exception("Silky: Could not get Info_ValueLength from Platform");
		
		byte[] value = new byte[size];

		fixed (void* ptr = &value[0])
		{
			result = (ErrorCodes)Open.CL.GetPlatformInfo(platform, info, size, ptr, out nuint _);
			if (result != ErrorCodes.Success)
				throw new Exception("Silky: Could not get Info_Value from Platform");
		}

		return Encoding.Default.GetString(value);
	}

	#endregion Platform Query Functions

	#region Device Query Functions

	public unsafe static byte[] GetDeviceInfo(IntPtr device, DeviceInfo info)
	{
		nuint size = 0;

		ErrorCodes result = (ErrorCodes)Open.CL.GetDeviceInfo(device, info, 0, null, out size);

		if (result != ErrorCodes.Success)
			throw new Exception("Silky: Could not get Info_ValueLength from Device");

		byte[] value = new byte[size];

		fixed (void* ptr = &value[0])
		{
			result = (ErrorCodes)Open.CL.GetDeviceInfo(device, info, size, ptr, out nuint _);
			if (result != ErrorCodes.Success)
				throw new Exception("Silky: Could not get Info_Value from Device");
		}

		return value;
	}

	public unsafe static string GetDeviceInfo_String(IntPtr device, DeviceInfo info)
		=> Encoding.Default.GetString(GetDeviceInfo(device, info));

	public unsafe static Int64 GetDeviceInfo_Int64(IntPtr device, DeviceInfo info)
		=> BitConverter.ToInt64(GetDeviceInfo(device, info));

	public unsafe static UInt64 GetDeviceInfo_UInt64(IntPtr device, DeviceInfo info)
		=> BitConverter.ToUInt64(GetDeviceInfo(device, info));

	public unsafe static Int32 GetDeviceInfo_Int32(IntPtr device, DeviceInfo info)
		=> BitConverter.ToInt32(GetDeviceInfo(device, info));

	#endregion Device Query Functions

	#region Regex Helper

	public static string ConvertWildcardToRegex(string value)
		=> "^" + Regex.Escape(value).Replace("_", ".").Replace("\\*", ".*") + "$";

	#endregion Regex Helper
}
