# Ethiopian Grade 8 Results Bot

A Telegram bot that helps students query their Grade 8 exam results from Ethiopian regional education bureaus.

## Features

- 🔍 Search student results by registration number and name
- 📍 Support for multiple regions (Addis Ababa, Amhara, Oromia, SNNPR, etc.)
- 📊 Result statistics and performance tracking
- 💾 User subscription and notification system
- 🔐 Admin controls and moderation tools
- 🌍 Multi-language support (English & Amharic)
- 🎓 Result caching for faster lookups

## Deployment

### Quick Start with Railway

1. Create a GitHub repository
2. Connect to [Railway.app](https://railway.app)
3. Set environment variables:
   - `TELEGRAM_BOT_TOKEN` - Get from @BotFather on Telegram
   - `ZYTE_API_KEY` - Get from [Zyte.com](https://www.zyte.com)
   - `CHANNEL_ID` - Your Telegram channel (e.g., @amharictutorialclass)
   - `ADMIN_CHAT_ID` - Your admin user ID

### Local Development

```bash
# Clone repository
git clone <your-repo-url>
cd erebirr

# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Set environment variables
export TELEGRAM_BOT_TOKEN="your_token"
export ZYTE_API_KEY="your_key"

# Run bot
python grade8_optimized.py
```

## Environment Variables

| Variable | Description |
|----------|-------------|
| `TELEGRAM_BOT_TOKEN` | Your Telegram bot token from @BotFather |
| `ZYTE_API_KEY` | Zyte API key for web scraping |
| `CHANNEL_ID` | Telegram channel ID (default: @amharictutorialclass) |
| `ADMIN_CHAT_ID` | Admin user ID for notifications |

## Commands

- `/start` - Start using the bot
- `/feedback` - Send feedback
- `/stats` - View statistics (admin only)
- `/ban` - Ban a user (admin only)
- `/unban` - Unban a user (admin only)

## Requirements

- Python 3.10+
- Telegram Bot API
- Zyte API (for web scraping)

## License

MIT License

## Support

For issues or questions, contact @Tegene on Telegram.
