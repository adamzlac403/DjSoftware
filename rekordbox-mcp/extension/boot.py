from rekordbox_mcp.database import RekordboxDatabase
from extension.gui import Gui

async def boot():
    await bootRekordboxDatabase()

async def bootRekordboxDatabase():
    db = RekordboxDatabase()

    await db.connect()

    count = await db.get_track_count()
    
    print(f"Tracks: {count}")
    await bootGui(db)

async def bootGui(db: RekordboxDatabase):
    gui = Gui(db)
    await gui.startGui()
    
