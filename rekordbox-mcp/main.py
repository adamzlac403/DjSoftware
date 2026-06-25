import asyncio
from rekordbox_mcp.database import RekordboxDatabase
from extension.boot import boot
async def main():
 await boot()

asyncio.run(main())