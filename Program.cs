using System.Numerics;
using System.Runtime.InteropServices;
using OpenCL_Secp256k1.OpenCL;
using OpenCL_Secp256k1.OpenCL.Kernels;
using OpenCL_Secp256k1.Test;
using Silk.NET.OpenCL;
using Secp256k1Net;


// Welcome to programming with OpenCL, lets keep it simple

Console.Write("\nGenerating test... ");
TestGenerator gen = new TestGenerator();
gen.GenerateAddKeyHashSig();
Console.Write("Done!\n\n");

// Setup OpenCL context, first we select the platform (NVidia, AMD, Intel, Apple, etc.)
Platform? platform = Platform.GetPlatform("*Apple*", DeviceTypes.Gpu);

if (platform is null)
	throw new Exception($"No OpenCL Platform found. Valid choices: {string.Join(", ", Platform.GetPlatforms().Select(p => p.Vendor))}");

// Didn't get an GPU's check if we have other devices
if (platform.Devices.Length == 0)
{
	//platform.DeviceType = DeviceTypes.All;

	// Just throw an error, technically we could switch to a different type, but lets keep it simple
	if (platform.Devices.Length == 0)
		throw new Exception("No OpenCL Devices found (Platform='{platform.Vendor}')");
	else
		throw new Exception($"No OpenCL >>GPU<< Devices found (Platform='{platform.Vendor}'). Valid device type choices: {string.Join(", ", platform.Devices.Select(d => d.DeviceType.ToString()))}");
}

// Just get the first device (technically, we could use multiple devices, but lets keep it simple)
Device device = platform.Devices[0];

// Create our opencl context
nint context = OpenCLSharp.CreateContext(device);

int devices = Utilities.GetContextInfo_Int32(context, ContextInfo.NumDevices);

Console.WriteLine("=========================================================");
Console.WriteLine("Platform Vendor: " + platform.Vendor);
Console.WriteLine("Device Name: " + device.Name);
Console.WriteLine("Device Type: " + device.DeviceType);
Console.WriteLine("Device Global Memory: " + device.GlobalMemory / 1024 / 1024 + "MB");
Console.WriteLine("Computer Units: " + device.WorkGroupSize + " units");
Console.WriteLine("Context Devices: " + devices + " device" + (devices == 1 ? "" : "s"));
Console.WriteLine("=========================================================\n\n");






// Create our opencl command queue
nint command_queue = OpenCLSharp.CreateCommandQueue(context, device);


// Run our tests
Secp256k1_Int128_Tests.RunTests(device, context, command_queue);

Console.WriteLine("\n\nAll Done!");
