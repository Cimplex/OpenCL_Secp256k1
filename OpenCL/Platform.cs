using System.Text.RegularExpressions;
using Silk.NET.OpenCL;

namespace OpenCL_Secp256k1.OpenCL;

public class Platform
{
    public IntPtr Handle { get; }

    public string Vendor { get; }

    public bool IsValid { get; }

    private Device[]? __devices;
    public Device[] Devices
    {
        get
        {
            if (Handle == IntPtr.Zero)
                return Array.Empty<Device>();

            if (__devices is null)
                RefreshDevices();

            // After RefreshDevices, __devices is never null
            return __devices!;
        }
    }

    private DeviceType _deviceType;
    public DeviceTypes DeviceType
    {
        get => (DeviceTypes)_deviceType;
        set
        {
            DeviceType _value = (DeviceType)value;

            if (_value != _deviceType)
            {
                _deviceType = _value;

                if (Handle != IntPtr.Zero && __devices is not null)
                    RefreshDevices();
            }
        }
    }

    internal Platform()
    {
        Vendor = "Invalid Platform";
        IsValid = false;

        Handle = IntPtr.Zero;
        DeviceType = DeviceTypes.None;
    }

    public Platform(IntPtr platform, DeviceType deviceType)
    {
        Vendor = "Invalid Platform";
        IsValid = false;

        Handle = platform;
        DeviceType = (DeviceTypes)deviceType;

        try
        {
            Vendor = Utilities.GetPlatformInfo(platform, PlatformInfo.Vendor);
            IsValid = true;
        }
        catch { }
    }

    public static implicit operator IntPtr(Platform p) => p.Handle;

    public unsafe void RefreshDevices()
    {
        if (!IsValid)
            throw new Exception("This OpenCL platform is no longer valid");

        // Get Number of Devices for Platform
        IntPtr[] _devices = new IntPtr[0];
        Span<IntPtr> _devicesSpan = new Span<IntPtr>(_devices);

        uint numDevices = 0;
        Span<uint> numDevicesSpan = new Span<uint>(ref numDevices);

        // DeviceType and DeviceTypes have the same values
        ErrorCodes result = (ErrorCodes)Open.CL.GetDeviceIDs(Handle, _deviceType, 0, _devicesSpan, numDevicesSpan);
        if (result != ErrorCodes.Success)
            throw new Exception($"Silky: Failed to get OpenCL Device Count for Platform ({Vendor})");

        // Get  Devices for Platform
        IntPtr[] devices = new IntPtr[numDevices];

        uint _numDevices = 0;
        Span<uint> _numDevicesSpan = new Span<uint>(ref _numDevices);

        // DeviceType and DeviceTypes have the same values
        fixed (nint* ptr = &devices[0])
        {
            result = (ErrorCodes)Open.CL.GetDeviceIDs(Handle, _deviceType, numDevices, ptr, out uint _);
        }

        if (result != ErrorCodes.Success)
            throw new Exception($"Silky: Failed to get OpenCL Devices for Platform ({Vendor})");

        __devices = new Device[numDevices];

        for (int i = 0; i < numDevices; i += 1)
        {
            __devices[i] = new Device(devices[i]);
        }
    }

	public static Platform[] GetPlatforms(DeviceTypes deviceType = DeviceTypes.Gpu)
	{
		// Get Number of Platforms
		IntPtr[] _platforms = new IntPtr[0];
		Span<IntPtr> _platformsSpan = new Span<IntPtr>(_platforms);

		uint numPlatforms = 0;
		Span<uint> numPlatformsSpan = new Span<uint>(ref numPlatforms);

		ErrorCodes result = (ErrorCodes)Open.CL.GetPlatformIDs(0, _platformsSpan, numPlatformsSpan);
		if (result != ErrorCodes.Success)
			throw new Exception("Silky: Failed to get OpenCL Platform count");

		// Get List of Platforms
		IntPtr[] platforms = new IntPtr[numPlatforms];
		Span<IntPtr> platformsSpan = new Span<IntPtr>(platforms);

		uint _numPlatforms = 0;
		Span<uint> _numPlatformsSpan = new Span<uint>(ref _numPlatforms);

		result = (ErrorCodes)Open.CL.GetPlatformIDs(numPlatforms, platformsSpan, _numPlatformsSpan);
		if (result != ErrorCodes.Success)
			throw new Exception("Silky: Failed to get OpenCL Platforms");

		Platform[] platformHelpers = new Platform[numPlatforms];

		// Create platform helpers
		for (int i = 0; i < numPlatforms; i += 1)
		{
			platformHelpers[i] = new Platform(platforms[i], (DeviceType)deviceType);
		}

		return platformHelpers;
	}

	public static Platform? GetPlatform(string wildcard = "*Intel*", DeviceTypes deviceType = DeviceTypes.Gpu)
	{
		string regex = Utilities.ConvertWildcardToRegex(wildcard.ToLower());
		Platform[] platforms = GetPlatforms(deviceType);

		foreach (Platform platform in platforms)
			if (Regex.IsMatch(platform.Vendor.ToLower(), regex))
				return platform;

		return null;
	}
}

