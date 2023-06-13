using System.Text;
using Silk.NET.OpenCL;
using System.Text.RegularExpressions;

namespace OpenCL_Secp256k1.OpenCL;

public static class Utilities
{
	public static void error(string message)
	{
		throw new Exception(message);
	}

	#region Program Query Functions

	public unsafe static byte[] GetProgramBuildInfo(IntPtr program, IntPtr device, ProgramBuildInfo info)
	{
		nuint size = 0;

		ErrorCodes result = (ErrorCodes)Open.CL.GetProgramBuildInfo(program, device, info, 0, null, out size);

		if (result != ErrorCodes.Success)
			throw new Exception("Silky: Could not get Info_ValueLength from Program");

		byte[] value = new byte[size];

		fixed (void* ptr = &value[0])
		{
			result = (ErrorCodes)Open.CL.GetProgramBuildInfo(program, device, info, size, ptr, out nuint _);
			if (result != ErrorCodes.Success)
				throw new Exception("Silky: Could not get Info_Value from Program");
		}

		return value;
	}

	public unsafe static string GetProgramBuildInfo_String(IntPtr program, IntPtr device, ProgramBuildInfo info)
		=> Encoding.Default.GetString(GetProgramBuildInfo(program, device, info));

	public unsafe static Int32 GetProgramBuildInfo_Int32(IntPtr program, IntPtr device, ProgramBuildInfo info)
		=> BitConverter.ToInt32(GetProgramBuildInfo(program, device, info));

	#endregion Program Query Functions

	#region Context Query Functions

	public unsafe static byte[] GetContextInfo(IntPtr context, ContextInfo info)
	{
		nuint size = 0;

		ErrorCodes result = (ErrorCodes)Open.CL.GetContextInfo(context, info, 0, null, out size);

		if (result != ErrorCodes.Success)
			throw new Exception("Silky: Could not get Info_ValueLength from Context");

		byte[] value = new byte[size];

		fixed (void* ptr = &value[0])
		{
			result = (ErrorCodes)Open.CL.GetContextInfo(context, info, size, ptr, out nuint _);
			if (result != ErrorCodes.Success)
				throw new Exception("Silky: Could not get Info_Value from Context");
		}

		return value;
	}

	public unsafe static Int32 GetContextInfo_Int32(IntPtr device, ContextInfo info)
		=> BitConverter.ToInt32(GetContextInfo(device, info));

	#endregion Context Query Functions

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
