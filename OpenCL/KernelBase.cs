namespace OpenCL_Secp256k1.OpenCL;

public abstract class KernelBase
{
	protected readonly nuint[] GlobalWorkSize = new nuint[] { nuint.Zero, nuint.Zero, nuint.Zero };

	protected readonly nuint[] LocalWorkSize = new nuint[] { 1, 1, 1 };

	private char[][] _srcCache = Array.Empty<char[]>();
	private string[] _srcCacheNames = Array.Empty<string>();
	private uint[] _srcCacheLengths = Array.Empty<uint>();

	public abstract (string name, string path)[] KernelPaths { get; }

	protected abstract KernelLibrary KernelLibrary { get; init; }

	protected KernelLibrary CreateKernelLibrary()
	{
		if (_srcCache.Length == 0 && KernelPaths != null)
		{
			List<string> names = new List<string>();
			List<char[]> sources = new List<char[]>();
			List<uint> lengths = new List<uint>();

			foreach ((string name, string path) in KernelPaths)
			{
				// Add the name of the kernel to our list
				names.Add(name);

				// Read out the source file
				string source;

				try
				{
					using (Stream file = typeof(KernelBase).Assembly.GetManifestResourceStream(path)!)
					using (StreamReader reader = new StreamReader(file))
						source = reader.ReadToEnd();
				}
				catch
				{
					throw new Exception($"embedded resource does not exist: '{path}' ('{name}')");
				}

				//sources.Add(Marshal.StringToHGlobalAnsi(source));
				sources.Add(source.ToCharArray());
				lengths.Add((uint)source.Length);
			}

			_srcCache = sources.ToArray();
			_srcCacheNames = names.ToArray();
			_srcCacheLengths = lengths.ToArray();
		}

		return new KernelLibrary(_srcCacheNames, _srcCache, _srcCacheLengths);
	}
}
